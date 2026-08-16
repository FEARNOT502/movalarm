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
# 스캔이 주기보다 오래 걸려도 최소 이만큼은 쉰다. 연속 요청으로 차단당하지 않기 위한 하한선
MIN_SLEEP_SEC = int(os.getenv("CGV_MIN_SLEEP_SEC", "30"))
STATE_PATH = Path(os.getenv("CGV_STATE_PATH", "state.json"))
# 살아있음 신호를 이 간격(초)마다 디스코드로 보낸다. 0이면 끄기. 기본 1시간
HEARTBEAT_SEC = int(os.getenv("CGV_HEARTBEAT_SEC", "3600"))
DISCORD_WEBHOOK = os.getenv("DISCORD_WEBHOOK_URL", "").strip()
# 디스코드 API 는 User-Agent 를 요구한다. 디스코드 문서 권장 형식: DiscordBot ($url, $version)
DISCORD_UA = os.getenv(
    "CGV_DISCORD_UA",
    "DiscordBot (https://github.com/cgv-alarm, 1.0) cgv-alarm/1.0")
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
#
# CGV 는 [영화] > [상영 스펙 그룹] > [회차] 3단 구조다. 그런데 일반관과 특별관의
# 마크업이 달라서, 회차 하나만 봐서는 상영관 이름을 알 수 없는 경우가 있다.
#   - 일반관: 회차 안에 screenInfo_theater 가 있음        → "6관 (Laser)"
#   - 특별관: 회차 안에는 시간/좌석뿐이고, 상영관은 위쪽
#             스펙 줄에 있음                              → "IMAX관IMAX LASER 2D"
# 그래서 회차 자신 + 스펙 줄 + 영화 블록을 각각 따로 잡고,
# 필터링은 이 셋을 전부 이어붙인 match 문자열로 한다. 마크업이 또 바뀌어도
# 상영관 이름이 어딘가에 남아 있으면 놓치지 않는다.
JS_EXTRACT = """
() => {
  const txt = e => e ? e.textContent.trim().replace(/\\s+/g, ' ') : '';
  const pick = (root, frag) => txt(root.querySelector(`[class*="${frag}"]`));

  return [...document.querySelectorAll('[class*="screenInfo_timeItem"]')].map(it => {
    // 영화 블록: closest 로 잡으면 이 회차가 속한 영화만 정확히 걸린다
    const wrap = it.closest('[class*="screenInfo_cinemaMovieWrap"]');
    const movie = wrap ? pick(wrap, 'screenInfo_title') : '';

    // 스펙 줄: 회차 안 → 없으면 영화 블록 아래 조상들에서 (영화 블록은 넘지 않는다)
    let spec = pick(it, 'screenInfo_title');
    if (!spec) {
      for (let p = it.parentElement; p && p !== wrap && p !== document.body; p = p.parentElement) {
        const t = p.querySelector('[class*="screenInfo_title"]');
        if (t) { spec = txt(t); break; }
      }
    }
    if (spec === movie) spec = '';

    // 상영관: 회차 안 → 없으면 스펙 줄에 상영관 이름이 붙어 있다
    let hall = pick(it, 'screenInfo_theater');
    if (!hall && wrap) {
      for (let p = it.parentElement; p && p !== wrap && p !== document.body; p = p.parentElement) {
        const t = p.querySelector('[class*="screenInfo_theater"]');
        if (t) { hall = txt(t); break; }
      }
    }
    if (!hall) hall = spec;

    const raw = txt(it);
    return {
      movie, spec, hall, raw,
      start:  pick(it, 'screenInfo_start'),
      end:    pick(it, 'screenInfo_end'),
      seats:  pick(it, 'screenInfo_seat'),
      status: pick(it, 'screenInfo_status'),
      match:  [movie, spec, hall, raw].join(' '),
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
    # User-Agent 를 반드시 넣어야 한다. urllib 기본값인 "Python-urllib/3.x" 는
    # 디스코드 앞단 Cloudflare 가 차단해서 403 (error code: 1010) 이 돌아온다.
    req = urllib.request.Request(
        DISCORD_WEBHOOK, data=payload,
        headers={"Content-Type": "application/json", "User-Agent": DISCORD_UA},
        method="POST")
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
    blank = {"seen": [], "bootstrapped": False, "last_heartbeat": 0}
    if not STATE_PATH.exists():
        return dict(blank)
    try:
        d = json.loads(STATE_PATH.read_text(encoding="utf-8"))
        for k, v in blank.items():
            d.setdefault(k, v)
        return d
    except Exception as e:  # noqa: BLE001
        log(f"상태 파일 손상, 새로 시작합니다: {e}")
        return dict(blank)


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
        spec = _clean(r.get("spec"))
        start = _clean(r.get("start"))
        end = re.sub(r"^[~\-–\s]+", "", _clean(r.get("end")))  # "- 13:05" / "~13:05" 정리
        hall = _clean(r.get("hall"))
        seats = _clean(r.get("seats"))

        # 상영관/좌석이 한 덩어리로 들어오는 날이 있어 시간·좌석 표기는 걷어낸다
        hall = re.sub(r"\d{1,2}:\d{2}\s*[-~]?\s*\d{0,2}:?\d{0,2}", " ", hall)
        hall = re.sub(r"(매진|\d[\d,]*\s*/\s*)?\d[\d,]*\s*석", " ", hall)
        hall = _clean(re.sub(r"(매진|조조|심야|브런치)", " ", hall))

        # 구조 파싱이 어긋나도 알림 자체는 나가도록 원문에서 최소한을 건져낸다
        if not movie:
            movie = spec or raw[:60]
        if not start:
            m = re.search(r"\b([0-2]?\d:[0-5]\d)\b", raw)
            start = m.group(1) if m else ""
        if not hall:
            hall = spec or raw

        rows.append({
            "date": ymd, "movie": movie, "spec": spec, "start": start, "end": end,
            "hall": hall, "seats": seats, "status": _clean(r.get("status")),
            "raw": raw, "match": _clean(r.get("match")) or raw, "url": url,
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

        # 구조가 또 바뀌었을 때 한 번에 파악하려고 회차 하나의 조상 사슬을 찍어둔다
        outline = page.evaluate("""() => {
          const it = document.querySelector('[class*="screenInfo_timeItem"]');
          if (!it) return [];
          const names = e => String(e.className).split(/\\s+/)
              .map(c => (c.match(/^(.+?)__/) || [,c])[1]).join(',');
          const out = [];
          let d = 0;
          for (let p = it; p && p !== document.body && d < 6; p = p.parentElement, d++) {
            out.push(`${'  '.repeat(d)}<${p.tagName.toLowerCase()} ${names(p)}> `
                     + p.textContent.trim().replace(/\\s+/g,' ').slice(0, 90));
          }
          return out;
        }""")
        log("--- 회차 하나의 조상 구조 (안쪽 → 바깥쪽) ---")
        for line in outline:
            log("  " + line)

        sample = page.evaluate(JS_EXTRACT)
        log(f"--- 실제 파싱 결과 {len(sample)}건 (앞 5건) ---")
        for r in sample[:5]:
            log(f"  {r['start']}~{r['end']} | 영화={r['movie']} | 관={r['hall']} | "
                f"스펙={r['spec']} | 좌석={r['seats']} | {r['status']}")

        halls: dict[str, int] = {}
        for r in sample:
            halls[_clean(r.get("hall")) or "(없음)"] = halls.get(_clean(r.get("hall")) or "(없음)", 0) + 1
        log(f"--- 이 날짜의 상영관 목록 {len(halls)}종 ---")
        for h, n in sorted(halls.items(), key=lambda x: -x[1]):
            mark = "  ← 필터 일치" if any(
                p.strip().lower() in h.lower() for p in HALL_PATTERN.split("|") if p.strip()) else ""
            log(f"  {n:3d}회차  {h}{mark}")
        if not any(p.strip().lower() in " ".join(halls).lower()
                   for p in HALL_PATTERN.split("|") if p.strip()):
            log(f"  → 오늘은 '{HALL_PATTERN}' 편성이 없습니다. 다른 날짜는 --debug 로 확인하세요.")

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
    """상영관 이름이 회차 안에 있을 때도, 위쪽 스펙 줄에만 있을 때도 잡히도록
    movie/spec/hall/raw 를 전부 이어붙인 문자열에서 찾는다."""
    pats = [p.strip().lower() for p in HALL_PATTERN.split("|") if p.strip()]
    hay = " ".join(str(row.get(k, "")) for k in ("match", "hall", "spec", "movie", "raw")).lower()
    return any(p in hay for p in pats)


def key_of(row: dict) -> str:
    return f"{row['date']}|{row['movie']}|{row['start']}|{row['hall']}"


def scan(debug: bool = False, stats: dict | None = None) -> list[dict]:
    """감시 기간 전체를 훑어 대상 특별관 회차 목록을 반환.

    stats 를 넘기면 전체 회차 수/조회한 날짜 수/오류 수를 채워준다 (하트비트용).
    """
    today = datetime.now(KST).date()
    found: list[dict] = []
    st = stats if stats is not None else {}
    st.update({"total": 0, "days": 0, "errors": 0, "seconds": 0.0})
    started = time.time()
    all_halls: dict[str, int] = {}
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
                    st["errors"] += 1
                    continue

                st["days"] += 1
                st["total"] += len(rows)

                # 어떤 상영관이든 회차가 0건이면 아직 예매 범위 밖
                empty_streak = empty_streak + 1 if not rows else 0
                if STOP_AFTER_EMPTY and empty_streak >= STOP_AFTER_EMPTY:
                    log(f"{ymd}까지 빈 날짜 {empty_streak}일 연속 → 예매 범위 끝으로 보고 중단")
                    break

                hits = rows if debug else [r for r in rows if matches_hall(r)]
                if debug:
                    for r in rows:
                        h = r.get("hall") or "(없음)"
                        all_halls[h] = all_halls.get(h, 0) + 1
                    log(f"{ymd}: 전체 {len(rows)}회차 / {HALL_PATTERN} 매칭 "
                        f"{len([r for r in rows if matches_hall(r)])}건")
                    for r in rows[:8]:
                        mk = " ★" if matches_hall(r) else ""
                        log(f"   · {r['start']} [{r['hall']}] {r['movie']} "
                            f"/ 스펙={r['spec']} / {r['seats']}{mk}")
                elif hits:
                    log(f"{ymd}: {HALL_PATTERN} {len(hits)}회차 확인")

                found.extend(hits)
                # 사람처럼 보이게 요청 간 간격을 조금씩 흔든다
                time.sleep(random.uniform(0.8, 2.0))
        finally:
            ctx.close()
            browser.close()
            st["seconds"] = time.time() - started

    if debug and all_halls:
        log("=" * 50)
        log(f"조회 기간 전체 상영관 목록 {len(all_halls)}종")
        pats = [p.strip().lower() for p in HALL_PATTERN.split("|") if p.strip()]
        for h, n in sorted(all_halls.items(), key=lambda x: -x[1]):
            mark = "  ← 필터 일치" if any(p in h.lower() for p in pats) else ""
            log(f"  {n:4d}회차  {h}{mark}")
        if not any(p in " ".join(all_halls).lower() for p in pats):
            log(f"  → 조회 기간 안에 '{HALL_PATTERN}' 편성이 전혀 없습니다.")
            log(f"     상영관 표기가 위 목록과 다르면 CGV_HALL_PATTERN 을 맞춰주세요.")
    return found


# ----------------------------------------------------------------------------
# 1회 검사
# ----------------------------------------------------------------------------
def _heartbeat(state: dict, rows: list[dict], stats: dict, kind: str) -> None:
    """살아있다는 신호를 디스코드로 보낸다. kind: 'start' | 'hourly'"""
    now = datetime.now(KST)
    health = "정상" if stats.get("errors", 0) == 0 else f"오류 {stats['errors']}건"
    body = (
        f"CGV {SITE_NM} · 필터 `{HALL_PATTERN}`\n"
        f"조회 {stats.get('days', 0)}일치 / 전체 {stats.get('total', 0)}회차 중 "
        f"**{HALL_PATTERN} {len(rows)}회차**\n"
        f"수집 상태: {health} · {now:%m-%d %H:%M} KST"
    )
    if kind == "start":
        msg = f"🟢 **알리미 감시 시작**\n{body}\n{INTERVAL_SEC // 60}분마다 확인합니다."
    else:
        msg = f"🩺 **정상 작동 중**\n{body}"

    if stats.get("days", 0) and stats.get("total", 0) == 0:
        msg += "\n⚠️ 전체 회차가 0건입니다. 차단이거나 셀렉터가 어긋났을 수 있으니 `--probe`로 확인하세요."

    if send_discord(msg):
        state["last_heartbeat"] = int(time.time())
        save_state(state)
        log(f"하트비트 발송 ({kind})")
    else:
        log(f"하트비트 발송 실패 ({kind})")


def check_once(announce_start: bool = False) -> int:
    state = load_state()
    seen = set(state["seen"])
    stats: dict = {}
    rows = scan(stats=stats)
    new = [r for r in rows if key_of(r) not in seen]

    # 살아있음 신호: 시작할 때 1회 + 이후 HEARTBEAT_SEC 마다
    if HEARTBEAT_SEC > 0:
        last = int(state.get("last_heartbeat", 0))
        if announce_start:
            _heartbeat(state, rows, stats, "start")
        elif time.time() - last >= HEARTBEAT_SEC:
            _heartbeat(state, rows, stats, "hourly")

    log(f"스캔 완료: {stats.get('days', 0)}일 / 전체 {stats.get('total', 0)}회차 "
        f"/ {HALL_PATTERN} {len(rows)}회차 / {stats.get('seconds', 0):.0f}초")

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
            lines.append(f"  • `{r['start']}{tail}` **{r['movie']}**  ({meta})")
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
    ap.add_argument("--announce-start", action="store_true",
                    help="이번 실행에서 '감시 시작' 알림을 1회 보낸다")
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
        first = True
        while True:
            t0 = time.time()
            try:
                check_once(announce_start=first)
                first = False
            except KeyboardInterrupt:
                log("종료합니다.")
                break
            except Exception as e:  # noqa: BLE001
                log(f"검사 중 오류: {type(e).__name__}: {str(e)[:200]}")
            # 스캔에 쓴 시간을 빼야 설정한 주기가 실제 주기가 된다.
            # 고정으로 자면 (스캔시간 + 주기) 가 되어 설정값보다 한참 느려진다.
            elapsed = time.time() - t0
            wait = INTERVAL_SEC - elapsed + random.uniform(-10, 10)
            if wait < MIN_SLEEP_SEC:
                log(f"스캔이 {elapsed:.0f}초 걸려 주기({INTERVAL_SEC}초)를 채웠습니다. "
                    f"{MIN_SLEEP_SEC}초만 쉬고 계속합니다.")
                wait = MIN_SLEEP_SEC
            time.sleep(wait)
        sys.exit(0)

    check_once(announce_start=args.announce_start)


if __name__ == "__main__":
    main()
