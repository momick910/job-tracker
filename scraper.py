#!/usr/bin/env python3
"""Job Tracker — ECB Direct + EuroBrussels aggregator."""

from __future__ import annotations

import hashlib
import html
import json
import os
import re
import smtplib
import time
import webbrowser
from collections import Counter
from datetime import datetime, timezone
from email.message import EmailMessage
from email.utils import formataddr
from pathlib import Path

import requests
from bs4 import BeautifulSoup

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

# ─── Config ───────────────────────────────────────────────────────────────────

JOBS_FILE   = Path("jobs.json")
REPORT_FILE = Path("report.html")
EB_BASE     = "https://www.eurobrussels.com"
REPORT_URL  = "https://momick910.github.io/job-tracker/report.html"

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
    )
}

SESSION = requests.Session()
SESSION.headers.update(HEADERS)

SOURCE_COLORS = {
    "ECB Direct":   "#003299",
    "EuroBrussels": "#c0392b",
}

LEVEL_BADGE_STYLE = {
    "Trainee":      "background:#ede9fe;color:#5b21b6",
    "Junior":       "background:#dcfce7;color:#166534",
    "Professional": "background:#dbeafe;color:#1e40af",
    "Senior":       "background:#fef3c7;color:#92400e",
    "Management":   "background:#fee2e2;color:#991b1b",
}

INST_FULL_NAMES: dict[str, str] = {
    "ECB":   "European Central Bank",
    "EIB":   "European Investment Bank",
    "EIF":   "European Investment Fund",
    "EBA":   "European Banking Authority",
    "ESMA":  "European Securities and Markets Authority",
    "EIOPA": "European Insurance and Occupational Pensions Authority",
    "ESRB":  "European Systemic Risk Board",
    "ESM":   "European Stability Mechanism",
    "EFSF":  "European Financial Stability Facility",
    "EP":    "European Parliament",
    "EC":    "European Commission",
    "EEAS":  "European External Action Service",
    "ECA":   "European Court of Auditors",
    "CJEU":  "Court of Justice of the European Union",
    "EUIPO": "European Union Intellectual Property Office",
    "EPSO":  "European Personnel Selection Office",
    "SRB":   "Single Resolution Board",
    "SSM":   "Single Supervisory Mechanism",
    "BIS":   "Bank for International Settlements",
    "IMF":   "International Monetary Fund",
}

# ─── Utilities ────────────────────────────────────────────────────────────────

def expand_institution(name: str) -> str:
    """Return 'ABBREV — Full Name' when name is a known bare abbreviation; otherwise unchanged."""
    if not name:
        return name
    if " - " in name or " — " in name or " – " in name:
        return name  # already includes full name
    upper = name.strip().upper()
    full = INST_FULL_NAMES.get(upper)
    return f"{name.strip()} — {full}" if full else name


def get_keywords() -> list:
    raw = os.environ.get("JOB_KEYWORDS", "")
    return [k.strip().lower() for k in raw.split(",") if k.strip()]


def job_id(job: dict) -> str:
    key = f"{job.get('institution')}|{job.get('title')}|{job.get('url')}"
    return hashlib.sha1(key.encode()).hexdigest()[:16]


def matches_keywords(job: dict, keywords: list) -> bool:
    text = " ".join([
        job.get("title", ""), job.get("department", ""),
        job.get("institution", ""), job.get("prerequisites", ""),
    ]).lower()
    return any(kw in text for kw in keywords)


def fetch(url: str, timeout: int = 20):
    try:
        r = SESSION.get(url, timeout=timeout, allow_redirects=True)
        r.raise_for_status()
        return BeautifulSoup(r.text, "html.parser")
    except requests.exceptions.Timeout:
        print(f"    [!] Timeout: {url}")
    except requests.exceptions.HTTPError as exc:
        print(f"    [!] HTTP {exc.response.status_code}: {url}")
    except requests.exceptions.ConnectionError:
        print(f"    [!] Connection error: {url}")
    except Exception as exc:
        print(f"    [!] {type(exc).__name__}: {url}")
    return None


def t(el, default: str = "") -> str:
    return el.get_text(strip=True) if el else default


def clean(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def trunc(s: str, n: int = 60) -> str:
    s = str(s or "")
    return s[:n] + "…" if len(s) > n else s


def format_salary(salary: str) -> str:
    if not salary:
        return ""
    # ECB grade band + net monthly: "F/G (bracket 1 - step 1) ... monthly net salary: €7,465..."
    m = re.match(r"^([A-J](?:/[A-J])?)\s*\([^)]*\)[^€]*(€[\d,]+)", salary, re.IGNORECASE)
    if m:
        return f"{m.group(1)} band — {m.group(2)}/mo net"
    # ECB traineeship grant: "The trainee grant is €1,170 per month..."
    m = re.match(r"[Tt]he trainee grant is (€[\d,]+)", salary)
    if m:
        return f"Grant: {m.group(1)}/mo"
    return trunc(salary, 70)


# ─── Entry level inference ────────────────────────────────────────────────────

# ECB salary grade → level.  Bands A–J from ECB pay scale.
_GRADE_LEVELS = {
    "A": "Junior", "B": "Junior",
    "C": "Professional", "D": "Professional", "E": "Professional",
    "F": "Senior", "G": "Senior", "H": "Senior",
    "I": "Management", "J": "Management",
}

_MANAGEMENT_KW  = ("director", "head of", "chief ", "secretary general", "managing director", "vp ", "vice president")
_SENIOR_KW      = ("senior ", "lead ", "team lead", "team leader", "principal ", "sr.")
_JUNIOR_KW      = ("junior ", "entry-level", "entry level", "graduate trainee")
_TRAINEE_KW     = ("traineeship", "trainee", " intern ", "internship", "phd trainee")


def infer_entry_level(title: str, grade: str = "", contract_type: str = "") -> str:
    tl = title.lower()
    ct = contract_type.lower()

    if any(kw in tl for kw in _TRAINEE_KW) or "traineeship" in ct:
        return "Trainee"
    if grade:
        first_band = grade.upper().split("/")[0].strip()
        if first_band in _GRADE_LEVELS:
            return _GRADE_LEVELS[first_band]
    if any(kw in tl for kw in _MANAGEMENT_KW):
        return "Management"
    if any(kw in tl for kw in _SENIOR_KW):
        return "Senior"
    if any(kw in tl for kw in _JUNIOR_KW):
        return "Junior"
    return "Professional"


def parse_grade(salary_text: str) -> str:
    """Extract 'F/G' or 'I' from 'F/G (bracket 1 - step 1) ...'"""
    m = re.match(r"^([A-J](?:/[A-J])?)\b", salary_text.strip())
    return m.group(1) if m else ""


def extract_prerequisites(value_el) -> str:
    """Pull essential requirements from the qualifications block."""
    if value_el is None:
        return ""
    full = clean(value_el.get_text(" "))
    # Try to isolate 'Essential:' section
    m = re.search(r"Essential[:\s]+(.*?)(?:Desired[:\s]|$)", full, re.DOTALL | re.IGNORECASE)
    text = clean(m.group(1)) if m else full
    return text[:320] + "…" if len(text) > 320 else text


# ─── ECB Direct ───────────────────────────────────────────────────────────────

def fetch_ecb_detail(url: str) -> dict:
    """Return a dict of detail fields from one ECB job page."""
    soup = fetch(url)
    if not soup:
        return {}

    aside = soup.find(class_="article--details")
    if not aside:
        return {}

    fields: dict = {}
    for p in aside.find_all("p", class_="paragraph"):
        label_el = p.find("span", {"data-map": "item-title"})
        if not label_el:
            continue
        label = clean(label_el.get_text())
        if not label or label == "General Information":
            continue
        value_els = p.find_all("span", {"data-map": "item-value"})
        if label == "Qualifications, experience and skills":
            # keep the raw element for structured extraction
            fields["_quals_el"] = value_els[0] if value_els else None
        else:
            fields[label] = clean(" ".join(v.get_text(" ") for v in value_els))

    result: dict = {}

    # Contract type
    result["contract_type"] = fields.get("Type of contract", "")

    # Who can apply
    result["who_can_apply"] = fields.get("Who can apply?", "")

    # Salary / grant + grade
    salary_text = fields.get("Salary", fields.get("Grant", ""))
    result["salary"] = salary_text
    result["grade"]  = parse_grade(salary_text)

    # Working time
    result["working_time"] = fields.get("Working time", "")

    # Role specialisation
    result["role_specialisation"] = fields.get("Role specialisation", "")

    # Prerequisites
    result["prerequisites"] = extract_prerequisites(fields.get("_quals_el"))

    return result


def scrape_ecb() -> list:
    """Scrape talent.ecb.europa.eu/careers, then fetch each detail page."""
    listing_url = "https://talent.ecb.europa.eu/careers"
    soup = fetch(listing_url)
    if not soup:
        return []

    cards = soup.find_all("article", class_="article--result")
    jobs  = []

    for card in cards:
        title_a = card.select_one("h3 a")
        if not title_a:
            continue
        title   = title_a.get_text(strip=True)
        job_url = title_a["href"].strip()

        subtitle   = card.select_one(".article__header__text__subtitle")
        department = ""
        deadline   = ""
        if subtitle:
            for div in subtitle.find_all("div"):
                icon   = div.find("span", class_=lambda c: c and "icon-" in c)
                spans  = div.find_all("span")
                value  = spans[-1].get_text(strip=True) if len(spans) >= 2 else ""
                if not icon or not value:
                    continue
                icls = " ".join(icon.get("class", []))
                if "businessArea" in icls:
                    department = value
                elif "calendar" in icls:
                    deadline = value

        # Fetch detail page for rich fields
        print(f"    Fetching detail: {title[:55]}")
        detail = fetch_ecb_detail(job_url)

        contract_type = detail.get("contract_type", "")
        grade         = detail.get("grade", "")

        jobs.append({
            "title":             title,
            "institution":       expand_institution("ECB"),
            "department":        department,
            "location":          detail.get("working_time", "") and "Frankfurt, Germany" or "Frankfurt, Germany",
            "deadline":          deadline,
            "posted":            "",
            "contract_type":     contract_type,
            "who_can_apply":     detail.get("who_can_apply", ""),
            "salary":            detail.get("salary", ""),
            "grade":             grade,
            "working_time":      detail.get("working_time", ""),
            "role_specialisation": detail.get("role_specialisation", ""),
            "prerequisites":     detail.get("prerequisites", ""),
            "tags":              [],
            "description":       "",
            "entry_level":       infer_entry_level(title, grade, contract_type),
            "url":               job_url,
            "source":            "ECB Direct",
        })

    return jobs


# ─── EuroBrussels ─────────────────────────────────────────────────────────────

def parse_eurobrussels_dates(raw: str) -> tuple:
    """Return (deadline, posted) from EuroBrussels postedDate text."""
    raw = clean(raw)
    parts = re.split(r"(?=Posted\b)", raw, maxsplit=1)
    if len(parts) == 2:
        deadline_raw, posted_raw = parts
    else:
        deadline_raw, posted_raw = "", parts[0]
    return deadline_raw.strip(), posted_raw.strip()


def scrape_eurobrussels() -> list:
    """Scrape eurobrussels.com/job_search."""
    url  = f"{EB_BASE}/job_search"
    soup = fetch(url)
    if not soup:
        return []

    job_list = soup.find("ul", class_="searchList")
    if not job_list:
        print("  [!] EuroBrussels: ul.searchList not found")
        return []

    jobs = []
    valid_containers = {"premiumJobContainer", "highlightedJobContainer"}

    for li in job_list.find_all("li", recursive=False):
        if not set(li.get("class", [])) & valid_containers:
            continue

        h3 = li.find("h3")
        if not h3:
            continue
        a = h3.find("a")
        if not a:
            continue

        title   = a.get_text(strip=True)
        href    = a.get("href", "")
        job_url = (EB_BASE + href) if href.startswith("/") else href

        institution = expand_institution(t(li.find(class_="companyName")))
        location    = t(li.find(class_="location"))
        salary      = t(li.find(class_="salary"))
        posted_raw  = t(li.find(class_="postedDate"))
        deadline, posted = parse_eurobrussels_dates(posted_raw)

        # Brief description paragraph
        desc_p = li.find("p")
        description = clean(desc_p.get_text()) if desc_p else ""
        if len(description) > 200:
            description = description[:197] + "…"

        # Sector / type tags
        tags = [clean(b.get_text()) for b in li.find_all(class_="badge") if clean(b.get_text())]

        jobs.append({
            "title":             title,
            "institution":       institution,
            "department":        "",
            "location":          location,
            "deadline":          deadline,
            "posted":            posted,
            "contract_type":     "",
            "who_can_apply":     "",
            "salary":            salary,
            "grade":             "",
            "working_time":      "",
            "role_specialisation": "",
            "prerequisites":     "",
            "tags":              tags,
            "description":       description,
            "entry_level":       infer_entry_level(title),
            "url":               job_url,
            "source":            "EuroBrussels",
        })

    return jobs


# ─── Data pipeline ────────────────────────────────────────────────────────────

def load_previous() -> dict:
    if JOBS_FILE.exists():
        try:
            data = json.loads(JOBS_FILE.read_text(encoding="utf-8"))
            return {j["id"]: j for j in data if "id" in j}
        except Exception:
            pass
    return {}


def process(raw: list, previous: dict, keywords: list) -> list:
    now  = datetime.now(timezone.utc).isoformat()
    seen: set = set()
    result = []
    for job in raw:
        jid = job_id(job)
        if jid in seen:
            continue
        seen.add(jid)
        job["id"]         = jid
        job["is_new"]     = jid not in previous
        job["scraped_at"] = now
        if keywords:
            if not matches_keywords(job, keywords):
                continue
            job["keyword_match"] = True
        else:
            job["keyword_match"] = False
        result.append(job)
    return result


def save(jobs: list) -> None:
    JOBS_FILE.write_text(json.dumps(jobs, indent=2, ensure_ascii=False), encoding="utf-8")


# ─── HTML report ──────────────────────────────────────────────────────────────

def generate_report(jobs: list) -> None:
    total        = len(jobs)
    new_count    = sum(1 for j in jobs if j.get("is_new"))
    institutions = sorted({j["institution"] for j in jobs})
    levels       = ["Trainee", "Junior", "Professional", "Senior", "Management"]
    run_time     = datetime.now().strftime("%Y-%m-%d %H:%M")

    def esc(s) -> str:
        return html.escape(str(s or ""), quote=True)

    def row(label: str, value: str) -> str:
        if not value:
            return ""
        return f'<div class="ml">{esc(label)}</div><div class="mv">{esc(value)}</div>'

    def card(job: dict) -> str:
        source_color = SOURCE_COLORS.get(job.get("source", ""), "#374151")
        level        = job.get("entry_level", "Professional")
        lvl_style    = LEVEL_BADGE_STYLE.get(level, LEVEL_BADGE_STYLE["Professional"])

        # Badges
        badges = [
            f'<span class="bs" style="background:{source_color};color:#fff">{esc(job.get("source",""))}</span>',
            f'<span class="bl" style="{lvl_style}">{esc(level)}</span>',
        ]
        if job.get("is_new"):          badges.append('<span class="bn">New</span>')
        if job.get("keyword_match"):   badges.append('<span class="bm">Match</span>')

        # Key-value rows — only non-empty fields are rendered
        meta_rows = "".join(filter(None, [
            row("Location",       job.get("location", "")),
            row("Deadline",       job.get("deadline", "")),
            row("Contract",       trunc(job.get("contract_type", ""), 65)),
            row("Working time",   job.get("working_time", "")),
            row("Salary",         format_salary(job.get("salary", ""))),
            row("Department",     trunc(job.get("department", ""), 80)),
            row("Specialisation", trunc(job.get("role_specialisation", ""), 80)),
            row("Posted",         job.get("posted", "")),
            row("Who can apply",  trunc(job.get("who_can_apply", ""), 110)),
        ]))

        # Prerequisites (ECB) or brief description (EuroBrussels)
        extra = ""
        if job.get("prerequisites"):
            extra = (f'<div class="pb">'
                     f'<div class="pl">Essential requirements</div>'
                     f'<div class="pt">{esc(job["prerequisites"])}</div>'
                     f'</div>')
        elif job.get("description"):
            extra = f'<div class="jd">{esc(job["description"])}</div>'

        # Sector tags (EuroBrussels)
        tags_html = ""
        if job.get("tags"):
            pills = "".join(f'<span class="tg">{esc(tg)}</span>' for tg in job["tags"])
            tags_html = f'<div class="jt">{pills}</div>'

        url = esc(job.get("url") or "#")

        return (
            f'<div class="jc"'
            f' data-source="{esc(job.get("source",""))}"'
            f' data-institution="{esc(job["institution"])}"'
            f' data-level="{esc(level)}"'
            f' data-new="{str(job.get("is_new", False)).lower()}"'
            f' data-title="{esc(job["title"].lower())}"'
            f' data-dept="{esc(job.get("department","").lower())}"'
            f' data-deadline="{esc(job.get("deadline",""))}">'
            f'<div class="jh">{"".join(badges)}</div>'
            f'<div class="jti">{esc(job["title"])}</div>'
            f'<div class="jin">{esc(job["institution"])}</div>'
            f'<div class="sp"></div>'
            f'<div class="mg">{meta_rows}</div>'
            f'{extra}{tags_html}'
            f'<div class="jf"><a class="vb" href="{url}" target="_blank" rel="noopener noreferrer">View job</a></div>'
            f'</div>'
        )

    source_opts = "\n    ".join(
        f'<option value="{esc(s)}">{esc(s)}</option>'
        for s in sorted({j.get("source", "") for j in jobs})
    )
    inst_opts = "\n    ".join(
        f'<option value="{esc(i)}">{esc(i)}</option>' for i in institutions
    )
    level_opts = "\n    ".join(
        f'<option value="{esc(lv)}">{esc(lv)}</option>' for lv in levels
    )
    cards_html = "\n".join(card(j) for j in jobs)

    doc = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>EU Job Tracker</title>
<style>
*,*::before,*::after{{box-sizing:border-box;margin:0;padding:0}}
body{{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif;background:#f0f4f8;color:#111827;min-height:100vh;-webkit-font-smoothing:antialiased}}

/* ── Page header ── */
.hdr{{background:linear-gradient(160deg,#0a1628 0%,#112040 55%,#162952 100%)}}
.hdr::before{{content:'';display:block;height:3px;background:linear-gradient(90deg,#2563eb 0%,#7c3aed 100%)}}
.hi{{max-width:860px;margin:0 auto;padding:2.75rem 1.5rem 2.5rem;display:flex;justify-content:space-between;align-items:center;gap:2.5rem}}
.hl{{flex:1;min-width:0}}
.hey{{font-size:.61rem;text-transform:uppercase;letter-spacing:.15em;color:#60a5fa;font-weight:700;margin-bottom:.55rem}}
.hdr h1{{font-size:2.2rem;font-weight:800;color:#f8fafc;letter-spacing:-.04em;line-height:1;margin-bottom:.5rem}}
.hint{{font-size:1.1rem;color:#94a3b8;margin-top:.9rem;padding-top:.9rem;border-top:1px solid rgba(148,163,184,.2);margin-bottom:.45rem;line-height:1.5}}
.hme{{font-size:.78rem;color:#475569}}
.hs{{display:flex;gap:1px;background:rgba(255,255,255,.06);border-radius:10px;overflow:hidden;flex-shrink:0;border:1px solid rgba(255,255,255,.07)}}
.hsi{{padding:1.2rem 1.75rem;text-align:center;min-width:90px}}
.hsi+.hsi{{border-left:1px solid rgba(255,255,255,.06)}}
.hsn{{font-size:2rem;font-weight:800;color:#f8fafc;letter-spacing:-.04em;line-height:1;margin-bottom:.35rem}}
.hsl{{font-size:.61rem;text-transform:uppercase;letter-spacing:.09em;color:#64748b;font-weight:600}}
@media(max-width:620px){{.hi{{flex-direction:column;align-items:flex-start;gap:1.5rem}}.hs{{width:100%}}.hsi{{flex:1}}}}

/* ── Filter bar ── */
.fb{{position:sticky;top:0;z-index:100;background:#fff;border-bottom:1px solid #e5e7eb;padding:1rem 1.5rem .8rem;box-shadow:0 2px 10px rgba(0,0,0,.06);display:flex;flex-direction:column;gap:.65rem}}
.fb-top{{display:flex;align-items:center}}
.fb-bot{{display:flex;align-items:center;gap:.45rem;flex-wrap:wrap}}
.si{{position:relative;width:100%}}
.si svg{{position:absolute;left:.8rem;top:50%;transform:translateY(-50%);pointer-events:none}}
#search{{width:100%;box-sizing:border-box;border:1.5px solid #e5e7eb;border-radius:10px;padding:.55rem .9rem .55rem 2.4rem;font-size:.9rem;outline:none;background:#f9fafb;color:#111827;transition:border-color .15s,box-shadow .15s}}
#search:focus{{border-color:#3b82f6;background:#fff;box-shadow:0 0 0 3px rgba(59,130,246,.1)}}
.fb select{{border:1.5px solid #e5e7eb;border-radius:8px;padding:.38rem 1.8rem .38rem .65rem;font-size:.81rem;outline:none;background:#f9fafb url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='11' height='11' viewBox='0 0 12 12'%3E%3Cpath d='M2 4l4 4 4-4' stroke='%239ca3af' stroke-width='1.6' stroke-linecap='round' stroke-linejoin='round' fill='none'/%3E%3C/svg%3E") no-repeat right .6rem center;color:#374151;cursor:pointer;appearance:none;-webkit-appearance:none;transition:border-color .15s,background-color .15s}}
.fb select:focus{{border-color:#3b82f6;background-color:#fff;box-shadow:0 0 0 3px rgba(59,130,246,.1)}}
#no-btn{{border:1.5px solid #e5e7eb;border-radius:8px;padding:.38rem .8rem;font-size:.81rem;cursor:pointer;background:#f9fafb;color:#374151;transition:all .15s;white-space:nowrap;user-select:none;line-height:1}}
#no-btn.on{{background:#dcfce7;border-color:#86efac;color:#166534;font-weight:600}}
#cl{{font-size:.76rem;color:#9ca3af;margin-left:auto;background:#f1f5f9;padding:.3rem .7rem;border-radius:20px;white-space:nowrap}}

/* ── Job list ── */
.grid{{max-width:860px;margin:1.5rem auto;padding:0 1.5rem 4rem;display:flex;flex-direction:column;gap:1rem}}

/* ── Card ── */
.jc{{background:#fff;border-radius:8px;padding:1.25rem 1.5rem;border:1px solid #e5e7eb;border-left:3px solid #e5e7eb;box-shadow:0 1px 2px rgba(0,0,0,.04);transition:box-shadow .15s,transform .12s}}
.jc:hover{{box-shadow:0 4px 14px rgba(0,0,0,.09);transform:translateY(-1px)}}
.jc[data-new="true"]{{border-left-color:#f59e0b}}

/* ── Badges ── */
.jh{{display:flex;align-items:center;gap:.35rem;margin-bottom:.65rem;flex-wrap:wrap}}
.bs,.bl,.bn,.bm{{font-size:.63rem;font-weight:700;padding:.2rem .52rem;border-radius:4px;letter-spacing:.04em;text-transform:uppercase;white-space:nowrap}}
.bn{{background:#fef3c7;color:#92400e}}
.bm{{background:#dbeafe;color:#1e40af}}

/* ── Title / institution ── */
.jti{{font-size:1.05rem;font-weight:700;color:#111827;line-height:1.3;margin-bottom:.18rem}}
.jin{{font-size:.83rem;font-weight:600;color:#2563eb;margin-bottom:.75rem}}

/* ── Separator ── */
.sp{{height:1px;background:#f3f4f6;margin-bottom:.7rem}}

/* ── Key-value meta grid ── */
.mg{{display:grid;grid-template-columns:105px 1fr;row-gap:.32rem;column-gap:.6rem;margin-bottom:.35rem}}
.ml{{font-size:.62rem;font-weight:700;text-transform:uppercase;letter-spacing:.07em;color:#9ca3af;padding-top:.12rem}}
.mv{{font-size:.84rem;color:#374151;line-height:1.4}}

/* ── Prerequisites block (ECB) ── */
.pb{{background:#f8fafc;border-left:2px solid #cbd5e1;border-radius:0 5px 5px 0;padding:.55rem .8rem;margin-top:.75rem}}
.pl{{font-size:.62rem;font-weight:700;text-transform:uppercase;letter-spacing:.07em;color:#64748b;margin-bottom:.3rem}}
.pt{{font-size:.81rem;color:#334155;line-height:1.55}}

/* ── Description (EuroBrussels) ── */
.jd{{font-size:.83rem;color:#6b7280;line-height:1.5;margin-top:.7rem;padding-top:.65rem;border-top:1px solid #f3f4f6}}

/* ── Tags ── */
.jt{{display:flex;gap:.3rem;flex-wrap:wrap;margin-top:.65rem}}
.tg{{font-size:.67rem;font-weight:500;background:#f1f5f9;color:#64748b;padding:.18rem .5rem;border-radius:4px}}

/* ── Footer ── */
.jf{{margin-top:.9rem;display:flex;justify-content:flex-end}}
.vb{{display:inline-block;background:#1d4ed8;color:#fff;font-size:.82rem;font-weight:600;padding:.42rem 1.1rem;border-radius:5px;text-decoration:none;letter-spacing:.01em;transition:background .15s}}
.vb:hover{{background:#1e40af}}
.empty{{text-align:center;padding:4rem 2rem;color:#9ca3af;font-size:.9rem}}
@media(max-width:580px){{.mg{{grid-template-columns:82px 1fr}}}}
</style>
</head>
<body>
<header class="hdr">
  <div class="hi">
    <div class="hl">
      <div class="hey">EU Institutions</div>
      <h1>Job Tracker</h1>
      <p class="hint">Hi Alejandra — here are the latest openings across EU institutions. New listings are highlighted.</p>
      <p class="hme">Updated {run_time} UTC</p>
    </div>
    <div class="hs">
      <div class="hsi"><div class="hsn">{total}</div><div class="hsl">Total jobs</div></div>
      <div class="hsi"><div class="hsn">{new_count}</div><div class="hsl">New this run</div></div>
      <div class="hsi"><div class="hsn">{len(institutions)}</div><div class="hsl">Institutions</div></div>
    </div>
  </div>
</header>
<div class="fb">
  <div class="fb-top">
    <div class="si">
      <svg width="15" height="15" viewBox="0 0 15 15" fill="none" xmlns="http://www.w3.org/2000/svg"><circle cx="6.5" cy="6.5" r="4.5" stroke="#9ca3af" stroke-width="1.4"/><path d="m10 10 2.5 2.5" stroke="#9ca3af" stroke-width="1.4" stroke-linecap="round"/></svg>
      <input type="search" id="search" placeholder="Search title, institution, department…" oninput="af()">
    </div>
  </div>
  <div class="fb-bot">
    <select id="sf" onchange="af()">
      <option value="">All sources</option>
      {source_opts}
    </select>
    <select id="lf" onchange="af()">
      <option value="">All levels</option>
      {level_opts}
    </select>
    <select id="inf" onchange="af()">
      <option value="">All institutions</option>
      {inst_opts}
    </select>
    <select id="so" onchange="af()">
      <option value="">Sort: default</option>
      <option value="deadline">Sort: deadline ↑</option>
      <option value="institution">Sort: institution</option>
      <option value="title">Sort: title</option>
    </select>
    <button id="no-btn" onclick="toggleNew()">✦ New only</button>
    <span id="cl">Showing {total} jobs</span>
  </div>
</div>
<div class="grid" id="grid">
{cards_html}
</div>
<script>
function toggleNew(){{
  var btn=document.getElementById('no-btn');
  btn.classList.toggle('on');
  af();
}}
function af(){{
  var q=document.getElementById('search').value.toLowerCase();
  var src=document.getElementById('sf').value;
  var lvl=document.getElementById('lf').value;
  var inst=document.getElementById('inf').value;
  var srt=document.getElementById('so').value;
  var nw=document.getElementById('no-btn').classList.contains('on');
  var g=document.getElementById('grid');
  var all=Array.from(g.querySelectorAll('.jc'));
  var vis=all.filter(function(c){{
    if(q&&c.dataset.title.indexOf(q)<0&&c.dataset.dept.indexOf(q)<0&&c.dataset.institution.toLowerCase().indexOf(q)<0)return false;
    if(src&&c.dataset.source!==src)return false;
    if(lvl&&c.dataset.level!==lvl)return false;
    if(inst&&c.dataset.institution!==inst)return false;
    if(nw&&c.dataset.new!=='true')return false;
    return true;
  }});
  if(srt==='deadline')vis.sort(function(a,b){{var da=a.dataset.deadline||'zzz',db=b.dataset.deadline||'zzz';return da<db?-1:da>db?1:0}});
  else if(srt==='institution')vis.sort(function(a,b){{return a.dataset.institution.localeCompare(b.dataset.institution)}});
  else if(srt==='title')vis.sort(function(a,b){{return a.dataset.title.localeCompare(b.dataset.title)}});
  all.forEach(function(c){{c.style.display='none'}});
  vis.forEach(function(c){{c.style.display='';g.appendChild(c)}});
  var ex=g.querySelector('.empty');if(ex)ex.remove();
  if(!vis.length){{var d=document.createElement('div');d.className='empty';d.textContent='No jobs match your filters.';g.appendChild(d)}}
  document.getElementById('cl').textContent='Showing '+vis.length+' of {total} jobs';
}}
</script>
</body>
</html>"""

    REPORT_FILE.write_text(doc, encoding="utf-8")
    webbrowser.open(REPORT_FILE.resolve().as_uri())
    print(f"  Report saved → {REPORT_FILE.resolve()}")


# ─── Email ────────────────────────────────────────────────────────────────────

def _build_email_html(new_jobs: list, has_new: bool, preheader: str, date_str: str) -> str:
    esc = html.escape

    if has_new:
        rows = []
        for j in new_jobs:
            title    = esc(j.get("title", ""))
            inst     = esc(j.get("institution", ""))
            deadline = esc(j.get("deadline", "") or "—")
            url      = esc(j.get("url", "#"))
            rows.append(
                f'<tr>'
                f'<td style="padding:8px;border-bottom:1px solid #eee;">{title}</td>'
                f'<td style="padding:8px;border-bottom:1px solid #eee;">{inst}</td>'
                f'<td style="padding:8px;border-bottom:1px solid #eee;">{deadline}</td>'
                f'<td style="padding:8px;border-bottom:1px solid #eee;"><a href="{url}" style="color:#111;">Apply</a></td>'
                f'</tr>'
            )
        content = (
            f'<h2 style="color:#111;">{len(new_jobs)} New EU Jobs · {esc(date_str)}</h2>'
            f'<table width="100%" cellpadding="8" cellspacing="0" border="0">'
            f'<tr style="background:#f5f5f5;">'
            f'<th align="left">Title</th><th align="left">Institution</th>'
            f'<th align="left">Deadline</th><th align="left">Apply</th>'
            f'</tr>'
            + "".join(rows)
            + "</table>"
        )
    else:
        content = (
            f'<h2 style="color:#111;">No New Jobs Today · {esc(date_str)}</h2>'
            f'<p style="color:#555;">Nothing new on the EU job market today — but great things are coming. '
            f'Keep going, you\'re doing amazing 🌟</p>'
        )

    return (
        f'<html><body style="font-family:Arial,sans-serif;background:#ffffff;padding:20px;">'
        f'<div style="display:none;max-height:0;overflow:hidden;">{esc(preheader)}</div>'
        f'{content}'
        f'<br>'
        f'<a href="{REPORT_URL}" style="background:#111;color:#fff;padding:12px 24px;text-decoration:none;border-radius:4px;">View Full Report</a>'
        f'</body></html>'
    )


def send_email(jobs: list) -> None:
    sender    = os.environ.get("GMAIL_ADDRESS", "").strip()
    password  = os.environ.get("GMAIL_APP_PASSWORD", "").strip()
    recip_raw = os.environ.get("EMAIL_RECIPIENTS", "").strip()

    if not (sender and password and recip_raw):
        print("  [email] Credentials not set — skipping.")
        return

    recipients = [r.strip() for r in recip_raw.split(",") if r.strip()]
    if not recipients:
        return

    new_jobs  = [j for j in jobs if j.get("is_new")]
    has_new   = bool(new_jobs)
    today     = datetime.now().strftime("%B %d, %Y")

    if has_new:
        subject   = f"[{len(new_jobs)}] New Positions at EU Institutions · {today}"
        preheader = ", ".join(j["title"] for j in new_jobs[:3])
    else:
        subject   = f"No New EU Jobs Today · {today}"
        preheader = "Nothing new today, but the full report is always available"

    body = _build_email_html(new_jobs, has_new, preheader, today)

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"]    = formataddr(("EU Job Tracker", sender))
    msg["To"]      = ", ".join(recipients)
    msg.set_content("Please view this email in an HTML-capable client.")
    msg.add_alternative(body, subtype="html")

    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
            smtp.login(sender, password)
            smtp.send_message(msg)
        print(f"  Email sent → {len(recipients)} recipient(s)")
    except Exception as exc:
        print(f"  [email] Send failed: {exc}")


# ─── Summary + main ───────────────────────────────────────────────────────────

def print_summary(jobs: list, elapsed: float) -> None:
    counts  = Counter(j["source"] for j in jobs)
    new_cnt = sum(1 for j in jobs if j.get("is_new"))
    W       = 46
    print(f"\n{'=' * W}")
    print(f"  EU Job Tracker — {elapsed:.1f}s")
    print(f"{'─' * W}")
    for src in sorted(counts):
        n   = counts[src]
        new = sum(1 for j in jobs if j["source"] == src and j.get("is_new"))
        suf = f"  +{new} new" if new else ""
        print(f"  {src:<28} {n:>3}{suf}")
    print(f"{'─' * W}")
    print(f"  Total  {len(jobs):>3}  |  {new_cnt} new")
    print(f"{'=' * W}\n")


def main() -> None:
    t0       = time.perf_counter()
    keywords = get_keywords()
    previous = load_previous()

    print(f"\nEU Job Tracker — {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    if keywords:
        print(f"Keywords: {', '.join(keywords)}")
    print(f"Previous run: {len(previous)} jobs\n")

    print("Scraping ECB Direct (talent.ecb.europa.eu)...")
    ecb_jobs = scrape_ecb()
    print(f"  Raw jobs found: {len(ecb_jobs)}")

    print("\nScraping EuroBrussels (eurobrussels.com/job_search)...")
    eb_jobs = scrape_eurobrussels()
    print(f"  Raw jobs found: {len(eb_jobs)}")

    jobs = process(ecb_jobs + eb_jobs, previous, keywords)
    save(jobs)

    print_summary(jobs, time.perf_counter() - t0)
    generate_report(jobs)
    send_email(jobs)


if __name__ == "__main__":
    main()
