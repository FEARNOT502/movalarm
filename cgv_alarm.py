#!/usr/bin/env python3
"""
CGV 특별관 예매 오픈 알리미
- 기본 감시 대상: CGV 센텀시티(siteNo=0089) IMAX
- 감지 기준: 해당 특별관에 없던 상영 회차가 새로 생기면 = 예매 오픈
- 알림: 디스코드 웹훅

실행 모드
  python cgv_alarm.py --once   : 1회 검사 후 종료 (cron / GitHub Actions 용)
  python cgv_alarm.py --loop   : 프로세스 상주하며 INTERVAL_SEC 마다 검사 (VM 용)
  python cgv_alarm.py --debug  : 필터 없이 긁힌 회차를 전부 출력 (셀렉터 점검용)
  python cgv_alarm.py --test   : 디스코드 웹훅 발송 테스트

필요 패키지
  pip install playwright && playwright install chromium
"""

from __future__ import annotations

import argparse
import json
import os
import random
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path

from playwright.sync_api import TimeoutError as PWTimeout
from playwright.sync_api import sync_playwright

# ----------------------------------------------------------------------------
# 설정 (환경변수로 덮어쓸 수 있음)
# ----------------------------------------------------------------------------
KST = timezone(timedelta(hours=9))

SITE_NO = os.getenv("CGV_SITE_NO", "0089")          # 센텀시티
SITE_NM = os.getenv("CGV_SITE_NM", "센텀시티")
# 회차의 상영관 표기에 이 문자열이 들어가면 대상으로 간주 (| 로 여러 개)
HALL_PATTERN = os.getenv("CGV_HALL_PATTERN", "IMAX")
HORIZON_DAYS = int(os.getenv("CGV_HORIZON_DAYS", "14"))   # 오늘부터 며칠 뒤까지 볼지
# 상영이 하나도 없는 날짜가 이만큼 연속되면 예매 가능 범위 끝으로 보고 조회 중단.
# CGV는 날짜를 연속 구간으로 여니까, 뒤쪽 빈 날짜까지 매번 긁을 이유가 없다. 0이면 끄기.
STOP_AFTER_EMPTY = int(os.getenv("CGV_STOP_AFTER_EMPTY", "3"))
INTERVAL_SEC = int(os.getenv("CGV_INTERVAL_SEC", "300"))  # --loop 주기 (기본 5분)
STATE_PATH = Path(os.getenv("CGV_STATE_PATH", "state.json"))
DISCORD_WEBHOOK = os.getenv("DISCORD_WEBHOOK_URL", "").strip()
HEADLESS = os.getenv("CGV_HEADLESS", "1") != "0"
NAV_TIMEOUT = int(os.getenv("CGV_NAV_TIMEOUT_MS", "30000"))
# 시간표가 안 뜨는 날짜는 이 시간만큼 기다린 뒤 '미편성'으로 넘긴다.
# 빈 날짜가 곧 대기 시간이라 전체 한 바퀴 소요시간을 좌우한다. 너무 줄이면 오탐이 난다.
WAIT_TABLE_MS = int(os.getenv("CGV_WAIT_TABLE_MS", "8000"))
WAIT_ITEM_MS = int(os.getenv("CGV_WAIT_ITEM_MS", "3000"))

BOOKING_URL = os.getenv("CGV_BOOKING_URL", "https://cgv.co.kr/cnm/movieBook/cinema")
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36")

# CGV는 Next.js SPA라 클래스명이 `screenInfo_timeItem__A1b2` 처럼
# 빌드마다 바뀌는 해시가 붙는다. 해시를 뺀 접두사로만 매칭해서 개편에 견디게 함.
#
# 2026-08 확인: 예전 `screenInfoTimes_*` 계열이 전부 사라지고 `screenInfo_*` 로 통합됐다.
# 영화 제목이 회차 항목 바깥(영화 블록)에 있어서, 회차에서 조상으로 거슬러 올라가며 찾는다.
SEL_TIMETABLE = '[class*="screenInfo_container"]'
SEL_ITEM = '[class*="screenInfo_timeItem"]'
SEL_TITLE = '[class*="screenInfo_title"]'
SEL_HALL = '[class*="screenInfo_theater"]'
SEL_SEAT = '[class*="screenInfo_seat"]'
SEL_START = '[class*="screenInfo_start"]'
SEL_END = '[class*="screenInfo_end"]'

# 회차 항목을 통째로 읽어오는 스크립트.
# 제목은 회차 안에 있으면 그대로 쓰고, 없으면 조상 중 제목을 가진 가장 가까운 블록에서 가져온다.
# 가장 가까운 조상을 쓰기 때문에 (영화 블록 > 전체 컨테이너) 다른 영화 제목을 집어오지 않는다.
JS_EXTRACT = """
() => {
  const txt = e => e ? e.textContent.trim().replace(/\\s+/g, ' ') : '';
  const pick = (root, frag) => txt(root.querySelector(`[class*="${frag}"]`));
  return [...document.querySelectorAll('[class*="screenInfo_timeItem"]')].map(it => {
    let movie = pick(it, 'screenInfo_title');
    if (!movie) {
      for (let p = it.parentElement; p && p !== document.body; p = p.parentElement) {
        const t = p.querySelector('[class*="screenInfo_title"]');
        if (t) { movie = txt(t); break; }
      }
    }
    return {
      movie,
      start:  pick(it, 'screenInfo_start'),
      end:    pick(it, 'screenInfo_end'),
      seats:  pick(it, 'screenInfo_seat'),
      hall:   pick(it, 'screenInfo_theater'),
      status: pick(it, 'screenInfo_status'),
      raw:    txt(it),
    };
  });
}
"""


def log(msg: str) -> None:
    print(f"[{datetime.now(KST):%Y-%m-%d %H:%M:%S}] {msg}", flush=True)


# ----------------------------------------------------------------------------
# 디스코드 알림
# ----------------------------------------------------------------------------
def send_discord(content: str) -> bool:
    if not DISCORD_WEBHOOK:
        log("!! DISCORD_WEBHOOK_URL 이 비어 있어 알림을 못 보냅니다.")
        return False
    payload = json.dumps({
        "username": "CGV 예매 알리미",
        "content": content[:1900],
        "allowed_mentions": {"parse": []},
    }).encode("utf-8")
    req = urllib.request.Request(
        DISCORD_WEBHOOK, data=payload,
        headers={"Content-Type": "application/json"}, method="POST")
    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=15) as r:
                if r.status in (200, 204):
                    return True
                log(f"디스코드 응답 코드 {r.status}")
        except urllib.error.HTTPError as e:
            body = e.read()[:200].decode("utf-8", "replace")
            log(f"디스코드 HTTP {e.code}: {body}")
            if e.code == 429:
                time.sleep(5 * (attempt + 1))
                continue
            return False
        except Exception as e:  # noqa: BLE001
            log(f"디스코드 전송 실패({attempt + 1}/3): {e}")
            time.sleep(3)
    return False


# ----------------------------------------------------------------------------
# 상태 저장 (이미 알린 회차 기억)
# ----------------------------------------------------------------------------
def load_state() -> dict:
    if not STATE_PATH.exists():
        return {"seen": [], "bootstrapped": False}
    try:
        d = json.loads(STATE_PATH.read_text(encoding="utf-8"))
        d.setdefault("seen", [])
        d.setdefault("bootstrapped", False)
        return d
    except Exception as e:  # noqa: BLE001
        log(f"상태 파일 손상, 새로 시작합니다: {e}")
        return {"seen": [], "bootstrapped": False}


def save_state(state: dict) -> None:
    # 지난 회차가 무한정 쌓이지 않게 오늘 이전 날짜 키는 정리
    today = datetime.now(KST).strftime("%Y%m%d")
    state["seen"] = sorted({k for k in state["seen"] if k.split("|", 1)[0] >= today})
    STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
    STATE_PATH.write_text(json.dumps(state, ensure_ascii=False, indent=1), encoding="utf-8")


# ----------------------------------------------------------------------------
# 크롤링
# ----------------------------------------------------------------------------
def _clean(s: str | None) -> str:
    return re.sub(r"\s+", " ", (s or "")).strip()


def parse_day(page, ymd: str) -> list[dict]:
    """해당 날짜의 모든 상영 회차를 긁어 리스트로 반환. 오픈 전이면 빈 리스트."""
    url = f"{BOOKING_URL}?siteNo={SITE_NO}&siteNm={SITE_NM}&scnYmd={ymd}"
    page.goto(url, wait_until="domcontentloaded", timeout=NAV_TIMEOUT)

    try:
        page.wait_for_selector(SEL_TIMETABLE, timeout=WAIT_TABLE_MS)
        page.wait_for_selector(SEL_ITEM, timeout=WAIT_ITEM_MS)
    except PWTimeout:
        return []  # 시간표 자체가 없음 = 아직 편성 안 됨 (정상 분기)

    page.wait_for_timeout(700)  # 렌더 안정화
    # 목록이 길면 뒤쪽이 지연 렌더링될 수 있어 한 번 끝까지 내렸다 올린다
    page.evaluate("() => window.scrollTo(0, document.body.scrollHeight)")
    page.wait_for_timeout(500)
    page.evaluate("() => window.scrollTo(0, 0)")

    rows: list[dict] = []
    for r in page.evaluate(JS_EXTRACT):
        raw = _clean(r.get("raw"))
        if not raw:
            continue

        movie = _clean(r.get("movie"))
        start = _clean(r.get("start"))
        end = re.sub(r"^[~\-–\s]+", "", _clean(r.get("end")))  # "- 13:05" / "~13:05" 정리
        hall = _clean(r.get("hall"))
        seats = _clean(r.get("seats"))

        # 구조 파싱이 어긋나도 알림 자체는 나가도록 원문에서 최소한을 건져낸다
        if not movie:
            movie = raw[:60]
        if not start:
            m = re.search(r"\b([0-2]?\d:[0-5]\d)\b", raw)
            start = m.group(1) if m else ""
        if not hall:
            hall = raw

        rows.append({
            "date": ymd, "movie": movie, "start": start, "end": end,
            "hall": hall, "seats": seats, "status": _clean(r.get("status")),
            "raw": raw, "url": url,
        })
    return rows


def probe() -> int:
    """페이지가 실제로 뭘 돌려주는지 눈으로 확인. 차단인지 셀렉터 문제인지 가른다."""
    ymd = datetime.now(KST).strftime("%Y%m%d")
    url = f"{BOOKING_URL}?siteNo={SITE_NO}&siteNm={SITE_NM}&scnYmd={ymd}"
    out = Path("probe")
    out.mkdir(exist_ok=True)

    with sync_playwright() as p:
        browser = p.chromium.launch(
            headless=HEADLESS,
            args=["--no-sandbox", "--disable-setuid-sandbox",
                  "--disable-dev-shm-usage", "--disable-blink-features=AutomationControlled"],
        )
        ctx = browser.new_context(
            user_agent=UA, locale="ko-KR", timezone_id="Asia/Seoul",
            viewport={"width": 1440, "height": 900},
        )
        page = ctx.new_page()
        log(f"조회 URL: {url}")
        resp = page.goto(url, wait_until="domcontentloaded", timeout=NAV_TIMEOUT)
        page.wait_for_timeout(6000)  # SPA 렌더링 대기

        status = resp.status if resp else None
        server = (resp.header_value("server") or "-") if resp else "-"
        cfray = (resp.header_value("cf-ray") or "-") if resp else "-"
        log(f"HTTP {status} / server={server} / cf-ray={cfray}")
        log(f"최종 URL: {page.url}")
        log(f"제목: {page.title()!r}")

        body = _clean(page.inner_text("body"))[:600]
        log(f"본문 앞부분: {body!r}")

        log("--- 셀렉터별 검출 개수 ---")
        counts = {}
        for name, sel in [("시간표 컨테이너", SEL_TIMETABLE), ("회차 항목", SEL_ITEM),
                          ("영화 제목", SEL_TITLE), ("상영관", SEL_HALL),
                          ("좌석", SEL_SEAT), ("시작시각", SEL_START)]:
            counts[name] = len(page.query_selector_all(sel))
            log(f"  {name:12s} {sel:48s} → {counts[name]}개")

        # 클래스명이 바뀌었는지 보려면 실제로 쓰인 클래스 접두사를 봐야 한다
        prefixes = page.evaluate("""() => {
            const s = new Set();
            document.querySelectorAll('[class]').forEach(e => {
                String(e.className).split(/\\s+/).forEach(c => {
                    const m = c.match(/^([A-Za-z]+_[A-Za-z]+)__/);
                    if (m) s.add(m[1]);
                });
            });
            return [...s].sort().slice(0, 60);
        }""")
        log(f"페이지에 쓰인 CSS Module 접두사 {len(prefixes)}종: {prefixes}")

        sample = page.evaluate(JS_EXTRACT)
        log(f"--- 실제 파싱 결과 {len(sample)}건 (앞 5건) ---")
        for r in sample[:5]:
            log(f"  {r['start']}~{r['end']} | {r['movie']} | 관={r['hall']} | "
                f"좌석={r['seats']} | {r['status']}")

        (out / "page.html").write_text(page.content(), encoding="utf-8")
        page.screenshot(path=str(out / "page.png"), full_page=True)
        log(f"probe/page.html, probe/page.png 저장 완료")

        browser.close()

    # 판정
    log("=" * 50)
    if status and status >= 400:
        log(f"진단: HTTP {status}. 실브라우저도 막혔습니다. 한국 IP로 옮기세요.")
        return 2
    if not prefixes:
        log("진단: CSS Module 클래스가 하나도 없습니다. CGV 화면이 아니라 차단/방어 페이지입니다.")
        log("      → 한국 IP(내 PC, Oracle 서울)로 옮기세요.")
        return 2
    if counts.get("회차 항목", 0) > 0:
        log("진단: 페이지도 셀렉터도 정상입니다. 회차가 0건이면 진짜로 편성이 없는 겁니다.")
        return 0
    if any(p.startswith("screenInfo") for p in prefixes):
        log("진단: CGV 시간표 페이지는 받았는데 회차 항목만 안 잡힙니다. 셀렉터 이름이 바뀌었습니다.")
        log(f"      → 위 접두사 목록에서 screenInfo 계열을 찾아 스크립트 상단 SEL_* 를 고치세요.")
        return 1
    log("진단: 페이지는 받았지만 시간표 영역 자체가 없습니다.")
    log("      → probe/page.png 를 열어 어떤 화면인지 직접 확인하세요. 지역선택/점검 화면일 수 있습니다.")
    return 1


def matches_hall(row: dict) -> bool:
    pats = [p.strip().lower() for p in HALL_PATTERN.split("|") if p.strip()]
    hay = f"{row.get('hall', '')} {row.get('raw', '')}".lower()
    return any(p in hay for p in pats)


def key_of(row: dict) -> str:
    return f"{row['date']}|{row['movie']}|{row['start']}|{row['hall']}"


def scan(debug: bool = False) -> list[dict]:
    """감시 기간 전체를 훑어 대상 특별관 회차 목록을 반환."""
    today = datetime.now(KST).date()
    found: list[dict] = []
    with sync_playwright() as p:
        browser = p.chromium.launch(
            headless=HEADLESS,
            args=["--no-sandbox", "--disable-setuid-sandbox",
                  "--disable-dev-shm-usage", "--disable-blink-features=AutomationControlled"],
        )
        ctx = browser.new_context(
            user_agent=UA, locale="ko-KR", timezone_id="Asia/Seoul",
            viewport={"width": 1440, "height": 900},
        )
        page = ctx.new_page()
        empty_streak = 0
        try:
            for i in range(HORIZON_DAYS):
                ymd = (today + timedelta(days=i)).strftime("%Y%m%d")
                try:
                    rows = parse_day(page, ymd)
                except Exception as e:  # noqa: BLE001
                    log(f"{ymd} 조회 실패: {type(e).__name__}: {str(e)[:120]}")
                    empty_streak = 0  # 오류는 '빈 날짜'와 다르니 카운트하지 않는다
                    continue

                # 어떤 상영관이든 회차가 0건이면 아직 예매 범위 밖
                empty_streak = empty_streak + 1 if not rows else 0
                if STOP_AFTER_EMPTY and empty_streak >= STOP_AFTER_EMPTY:
                    log(f"{ymd}까지 빈 날짜 {empty_streak}일 연속 → 예매 범위 끝으로 보고 중단")
                    break

                hits = rows if debug else [r for r in rows if matches_hall(r)]
                if debug:
                    log(f"{ymd}: 전체 {len(rows)}회차 / {HALL_PATTERN} 매칭 "
                        f"{len([r for r in rows if matches_hall(r)])}건")
                    for r in rows[:8]:
                        log(f"   · {r['start']} {r['movie']} | 관={r['hall']}")
                elif hits:
                    log(f"{ymd}: {HALL_PATTERN} {len(hits)}회차 확인")

                found.extend(hits)
                # 사람처럼 보이게 요청 간 간격을 조금씩 흔든다
                time.sleep(random.uniform(0.8, 2.0))
        finally:
            ctx.close()
            browser.close()
    return found


# ----------------------------------------------------------------------------
# 1회 검사
# ----------------------------------------------------------------------------
def check_once() -> int:
    state = load_state()
    seen = set(state["seen"])
    rows = scan()
    new = [r for r in rows if key_of(r) not in seen]

    if not rows:
        log(f"{SITE_NM} {HALL_PATTERN} 편성 없음 (아직 오픈 전)")
    if not new:
        if rows:
            log(f"신규 없음 (기존 {len(rows)}회차 유지)")
        return 0

    # 첫 실행은 기존 편성을 전부 '이미 본 것'으로 등록만 하고 알림은 생략
    if not state["bootstrapped"]:
        state["bootstrapped"] = True
        state["seen"] = sorted(seen | {key_of(r) for r in new})
        save_state(state)
        log(f"첫 실행: 현재 {len(new)}회차를 기준선으로 저장했습니다. (알림 생략)")
        return 0

    by_date: dict[str, list[dict]] = {}
    for r in new:
        by_date.setdefault(r["date"], []).append(r)

    lines = [f"🎬 **{SITE_NM} {HALL_PATTERN} 예매 오픈!**", ""]
    for d in sorted(by_date):
        pretty = f"{d[:4]}-{d[4:6]}-{d[6:]}"
        lines.append(f"__{pretty}__")
        for r in sorted(by_date[d], key=lambda x: x["start"]):
            tail = f" ~{r['end']}" if r["end"] else ""
            meta = " / ".join(x for x in (r["hall"], r.get("seats", "")) if x)
            lines.append(f"  • `{r['start']}{tail}` {r['movie']}  ({meta})")
        lines.append("")
    lines.append(f"<{new[0]['url']}>")
    msg = "\n".join(lines)

    print(msg)
    if send_discord(msg):
        log(f"디스코드 알림 발송 완료 (신규 {len(new)}회차)")
        state["seen"] = sorted(seen | {key_of(r) for r in new})
        save_state(state)
    else:
        log("알림 발송 실패 - 상태를 저장하지 않고 다음 검사에서 재시도합니다.")
    return len(new)


def main() -> None:
    ap = argparse.ArgumentParser(description="CGV 특별관 예매 오픈 알리미")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--once", action="store_true", help="1회 검사 후 종료")
    g.add_argument("--loop", action="store_true", help="주기적으로 계속 검사")
    g.add_argument("--debug", action="store_true", help="긁힌 회차를 전부 출력")
    g.add_argument("--test", action="store_true", help="디스코드 웹훅 발송 테스트")
    g.add_argument("--probe", action="store_true",
                   help="페이지 원본을 덤프해 차단인지 셀렉터 문제인지 진단")
    args = ap.parse_args()

    log(f"대상: CGV {SITE_NM}(siteNo={SITE_NO}) / 필터='{HALL_PATTERN}' / "
        f"{HORIZON_DAYS}일치 / 상태={STATE_PATH}")

    if args.test:
        ok = send_discord("✅ CGV 알리미 웹훅 연결 테스트입니다.")
        log("웹훅 정상" if ok else "웹훅 실패 - URL을 다시 확인하세요.")
        sys.exit(0 if ok else 1)

    if args.probe:
        sys.exit(probe())

    if args.debug:
        scan(debug=True)
        sys.exit(0)

    if args.loop:
        while True:
            try:
                check_once()
            except KeyboardInterrupt:
                log("종료합니다.")
                break
            except Exception as e:  # noqa: BLE001
                log(f"검사 중 오류: {type(e).__name__}: {str(e)[:200]}")
            wait = INTERVAL_SEC + random.uniform(-20, 20)
            time.sleep(max(60, wait))
        sys.exit(0)

    check_once()


if __name__ == "__main__":
    main()
