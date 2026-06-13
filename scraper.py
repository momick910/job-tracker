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
from playwright.sync_api import sync_playwright

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

# ─── Config ───────────────────────────────────────────────────────────────────

JOBS_FILE   = Path("jobs.json")
REPORT_FILE = Path("report.html")
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
    "EEAS":         "#003366",
    "Bruegel":      "#c0392b",
    "EU Commission":"#2e7d32",
    "EU Parliament":"#7b1fa2",
    "EU Council":   "#e65100",
    "EIB":          "#00695c",
    "OECD":         "#0277bd",
    "AIIB":         "#c62828",
    "ADB":          "#1565c0",
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


_EXP_KW = re.compile(r"experience|requirement|qualif|profile|background|degree|education", re.I)


def _extract_experience_snippet(html_text: str, max_len: int = 120) -> str:
    """Return a short experience/requirements snippet from job HTML content."""
    if not html_text:
        return ""
    soup = BeautifulSoup(html_text, "html.parser")
    # Prefer a sentence/paragraph that mentions experience keywords
    for el in soup.find_all(["p", "li"]):
        text = clean(el.get_text(" "))
        if len(text) > 25 and _EXP_KW.search(text):
            return text[:max_len] + ("…" if len(text) > max_len else "")
    # Fallback: first non-trivial paragraph
    for p in soup.find_all("p"):
        text = clean(p.get_text(" "))
        if len(text) > 30:
            return text[:max_len] + ("…" if len(text) > max_len else "")
    return ""


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

        prereqs = detail.get("prerequisites", "")
        jobs.append({
            "title":             title,
            "institution":       expand_institution("ECB"),
            "department":        department,
            "location":          "Frankfurt, Germany",
            "deadline":          deadline,
            "posted":            "",
            "contract_type":     contract_type,
            "who_can_apply":     detail.get("who_can_apply", ""),
            "salary":            detail.get("salary", ""),
            "grade":             grade,
            "working_time":      detail.get("working_time", ""),
            "role_specialisation": detail.get("role_specialisation", ""),
            "prerequisites":     prereqs,
            "experience":        trunc(prereqs, 120),
            "tags":              [],
            "description":       "",
            "entry_level":       infer_entry_level(title, grade, contract_type),
            "url":               job_url,
            "source":            "ECB Direct",
        })

    return jobs


# ─── Playwright helper ────────────────────────────────────────────────────────

def scrape_with_playwright(url: str, wait_for: str | None = None, wait_ms: int = 3000) -> str:
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        page = browser.new_page()
        page.goto(url, timeout=30000)
        if wait_for:
            page.wait_for_selector(wait_for, timeout=15000)
        else:
            page.wait_for_timeout(wait_ms)
        content = page.content()
        browser.close()
        return content


# ─── EEAS ─────────────────────────────────────────────────────────────────────

_EEAS_URLS = [
    "https://www.eeas.europa.eu/eeas/vacancies_en?f%5B0%5D=contract_type%3ATemporary%20Agent",
    "https://www.eeas.europa.eu/eeas/vacancies_en?f%5B0%5D=contract_type%3ATrainee",
    "https://www.eeas.europa.eu/eeas/vacancies_en?f%5B0%5D=contract_type%3AACSDP%20Mission%20post",
]


def scrape_eeas() -> list:
    """Scrape EEAS vacancies across three contract-type filter URLs via Playwright."""
    jobs: list = []
    seen_urls: set = set()

    for url in _EEAS_URLS:
        label = url.split("contract_type%3A")[-1]
        print(f"  Fetching EEAS [{label}]...")
        raw_html = scrape_with_playwright(url, wait_ms=5000)
        soup = BeautifulSoup(raw_html, "html.parser")

        # Try selectors in order of specificity
        job_els = (
            soup.select(".views-row")
            or soup.find_all("article")
            or [li for li in soup.find_all("li") if li.find("a", href=True)]
        )

        # Print the first element found so we can verify the selector
        if job_els:
            print(f"\n--- EEAS [{label}] first job element ---")
            print(str(job_els[0])[:1500])
            print("--- end ---\n")
        else:
            print(f"  [!] EEAS [{label}]: no job elements found")
            continue

        for el in job_els:
            a = el.find("a", href=True)
            if not a:
                continue
            title = clean(a.get_text())
            href = a["href"].strip()
            job_url = href if href.startswith("http") else f"https://www.eeas.europa.eu{href}"
            if not title or job_url in seen_urls:
                continue
            seen_urls.add(job_url)
            jobs.append({
                "title":               title,
                "institution":         expand_institution("EEAS"),
                "department":          "",
                "location":            "",
                "deadline":            "",
                "posted":              "",
                "contract_type":       label,
                "who_can_apply":       "",
                "salary":              "",
                "grade":               "",
                "working_time":        "",
                "role_specialisation": "",
                "prerequisites":       "",
                "experience":          "",
                "tags":                [],
                "description":         "",
                "entry_level":         infer_entry_level(title),
                "url":                 job_url,
                "source":              "EEAS",
            })

    return jobs


# ─── Bruegel ──────────────────────────────────────────────────────────────────

def scrape_bruegel() -> list:
    """Scrape bruegel.org/careers (plain HTML, no JS required)."""
    soup = fetch("https://www.bruegel.org/careers")
    if not soup:
        return []

    jobs = []
    for li in soup.find_all("li", attrs={"data-list-item-id": True}):
        a = li.find("a", href=True)
        if not a:
            continue
        title = clean(a.get_text())
        job_url = "https://www.bruegel.org" + a["href"].strip()

        # Deadline is the text node immediately after </a>, wrapped in parentheses
        deadline = "Rolling basis"
        for sibling in a.next_siblings:
            text = sibling if isinstance(sibling, str) else sibling.get_text()
            m = re.search(r"\(([^)]+)\)", text)
            if m:
                deadline = m.group(1).strip()
                break

        # Any remaining text in the <li> beyond title and deadline parenthetical
        full_text = clean(li.get_text(" "))
        leftover  = re.sub(re.escape(title), "", full_text, count=1)
        leftover  = re.sub(r"\([^)]*\)", "", leftover)
        experience = clean(leftover)
        experience = trunc(experience, 120) if experience else ""

        if not title:
            continue
        jobs.append({
            "title":               title,
            "institution":         expand_institution("Bruegel"),
            "department":          "",
            "location":            "Brussels, Belgium",
            "deadline":            deadline,
            "posted":              "",
            "contract_type":       "",
            "who_can_apply":       "",
            "salary":              "",
            "grade":               "",
            "working_time":        "",
            "role_specialisation": "",
            "prerequisites":       "",
            "experience":          experience,
            "tags":                [],
            "description":         "",
            "entry_level":         infer_entry_level(title),
            "url":                 job_url,
            "source":              "Bruegel",
        })

    print(f"  Bruegel jobs found: {len(jobs)}")
    return jobs


# ─── EU Commission ────────────────────────────────────────────────────────────

_EC_BASE_URL = (
    "https://eu-careers.europa.eu/en/job-opportunities/open-vacancies/ec_vacancies"
    "?field_epso_domain_target_id="
    "&field_epso_type_of_contract_target_id=770"
    "&field_epso_location_target_id=All"
)


def _parse_ec_page(soup) -> list:
    """Extract job dicts from one EC vacancies page."""
    jobs = []
    for td_title in soup.find_all("td", class_="views-field-title"):
        a = td_title.find("a", href=True)
        if not a:
            continue
        title = clean(a.get_text())
        job_url = "https://eu-careers.europa.eu" + a["href"].strip()

        row = td_title.parent

        td_domain = row.find("td", class_="views-field-field-epso-domain")
        domain = clean(td_domain.get_text()) if td_domain else ""

        td_deadline = row.find("td", class_="views-field-field-epso-deadline")
        deadline = ""
        if td_deadline:
            time_el = td_deadline.find("time")
            if time_el:
                deadline = time_el.get("datetime", clean(time_el.get_text()))

        if not title:
            continue
        jobs.append({
            "title":               title,
            "institution":         "EU Commission",
            "department":          domain,
            "location":            "Brussels, Belgium",
            "deadline":            deadline,
            "posted":              "",
            "contract_type":       "",
            "who_can_apply":       "",
            "salary":              "",
            "grade":               "",
            "working_time":        "",
            "role_specialisation": domain,
            "prerequisites":       "",
            "experience":          "",
            "tags":                [],
            "description":         "",
            "entry_level":         infer_entry_level(title),
            "url":                 job_url,
            "source":              "EU Commission",
        })
    return jobs


def scrape_eu_commission() -> list:
    """Scrape all pages of eu-careers.europa.eu open EC vacancies (plain HTML)."""
    jobs: list = []
    page = 0

    while True:
        url = f"{_EC_BASE_URL}&page={page}"
        soup = fetch(url)
        if not soup:
            break
        page_jobs = _parse_ec_page(soup)
        if not page_jobs:
            break
        jobs.extend(page_jobs)
        print(f"    Page {page + 1}: {len(page_jobs)} jobs")
        page += 1
        time.sleep(1)

    print(f"  EU Commission jobs found: {len(jobs)} across {page} page(s)")
    return jobs


# ─── EU Parliament ────────────────────────────────────────────────────────────

def scrape_eu_parliament() -> list:
    """Scrape apply4ep.gestmax.eu job listings via Playwright (JS-rendered)."""
    raw_html = scrape_with_playwright("https://apply4ep.gestmax.eu/search/lang/en_GB", wait_ms=3000)
    soup = BeautifulSoup(raw_html, "html.parser")

    job_els = soup.select(".gestmax-item")
    if not job_els:
        container = soup.find(class_=re.compile(r"result|listing|search", re.I))
        if container:
            job_els = container.find_all("li")

    if not job_els:
        print("  EU Parliament: no current openings")
        return []

    jobs = []
    for el in job_els:
        a = el.find("a", href=True)
        if not a:
            continue
        title = clean(a.get_text())
        href = a["href"].strip()
        job_url = href if href.startswith("http") else "https://apply4ep.gestmax.eu" + href

        time_el = el.find("time")
        if time_el:
            deadline = time_el.get("datetime", clean(time_el.get_text()))
        else:
            m = re.search(r"\b(\d{1,2}[./-]\d{1,2}[./-]\d{2,4}|\d{4}-\d{2}-\d{2})\b", el.get_text())
            deadline = m.group(1) if m else ""

        if not title:
            continue
        jobs.append({
            "title":               title,
            "institution":         "EU Parliament",
            "department":          "",
            "location":            "Brussels, Belgium",
            "deadline":            deadline,
            "posted":              "",
            "contract_type":       "",
            "who_can_apply":       "",
            "salary":              "",
            "grade":               "",
            "working_time":        "",
            "role_specialisation": "",
            "prerequisites":       "",
            "experience":          "",
            "tags":                [],
            "description":         "",
            "entry_level":         infer_entry_level(title),
            "url":                 job_url,
            "source":              "EU Parliament",
        })

    print(f"  EU Parliament jobs found: {len(jobs)}")
    return jobs


# ─── EU Council ───────────────────────────────────────────────────────────────

def scrape_eu_council() -> list:
    """Scrape talents.coe.int open positions (plain HTML)."""
    soup = fetch("https://talents.coe.int/en_GB/careersmarketplace/WidgetOpenPositions")
    if not soup:
        return []

    def _sibling_text(strong_el) -> str:
        """Return the text node that immediately follows a <strong> tag."""
        if not strong_el:
            return ""
        for sibling in strong_el.next_siblings:
            text = sibling if isinstance(sibling, str) else sibling.get_text()
            text = clean(text)
            if text:
                return text
        return ""

    jobs = []
    for article in soup.find_all("article", class_="article--card"):
        h3 = article.find("h3")
        if not h3:
            continue
        a = h3.find("a", class_="link", href=True)
        if not a:
            continue
        title = clean(a.get_text())
        job_url = a["href"].strip()

        duty_strong = article.find("strong", string=re.compile(r"Duty station", re.I))
        location = _sibling_text(duty_strong) or "See posting"

        contract_strong = article.find("strong", string=re.compile(r"Recruitment type", re.I))
        contract_type = _sibling_text(contract_strong)

        content_div = article.find("div", class_="article__content")
        experience = ""
        if content_div:
            for p in content_div.find_all("p"):
                text = clean(p.get_text(" "))
                if len(text) > 25:
                    experience = trunc(text, 120)
                    break

        if not title:
            continue
        jobs.append({
            "title":               title,
            "institution":         "EU Council",
            "department":          "",
            "location":            location,
            "deadline":            "See posting",
            "posted":              "",
            "contract_type":       contract_type,
            "who_can_apply":       "",
            "salary":              "",
            "grade":               "",
            "working_time":        "",
            "role_specialisation": "",
            "prerequisites":       "",
            "experience":          experience,
            "tags":                [],
            "description":         "",
            "entry_level":         infer_entry_level(title, contract_type=contract_type),
            "url":                 job_url,
            "source":              "EU Council",
        })

    print(f"  EU Council jobs found: {len(jobs)}")
    return jobs


# ─── EIB ──────────────────────────────────────────────────────────────────────

def scrape_eib() -> list:
    """Scrape EIB job postings from their Atom RSS feed."""
    import xml.etree.ElementTree as ET

    feed_url = (
        "https://erecruitment.eib.org/PSIGW/HttpListeningConnector/feeds/RealtimeQueryFeed"
        "?FEED_ID=ADMN_BEI_HRS_JOB_POSTING_RSS_1&S=P"
    )
    try:
        r = SESSION.get(feed_url, timeout=20)
        r.raise_for_status()
        root = ET.fromstring(r.content)
    except Exception as exc:
        print(f"  [!] EIB feed error: {exc}")
        return []

    # Atom namespace; age namespace for expires
    NS  = {"atom": "http://www.w3.org/2005/Atom"}
    AGE = "http://purl.org/atompub/age/1.0"

    # Strip the trailing "(Entity: EIB - Job ID: XXXXX)" suffix from titles
    _SUFFIX_RE = re.compile(r"\s*\(Entity:.*?\)\s*$", re.IGNORECASE)

    jobs = []
    for entry in root.findall("atom:entry", NS):
        raw_title = (entry.findtext("atom:title", "", NS) or "").strip()
        title = clean(_SUFFIX_RE.sub("", raw_title))

        link_el = entry.find("atom:link[@rel='alternate']", NS)
        if link_el is None:
            link_el = entry.find("atom:link", NS)
        job_url = link_el.get("href", "").strip() if link_el is not None else ""

        published = (entry.findtext("atom:published", "", NS) or "").strip()[:10]

        expires_el = entry.find(f"{{{AGE}}}expires")
        deadline = expires_el.text.strip()[:10] if expires_el is not None and expires_el.text else ""

        location = "Luxembourg" if "luxembourg" in title.lower() else "Brussels, Belgium"

        content_el = entry.find("atom:content", NS)
        content_html = content_el.text if content_el is not None and content_el.text else ""
        experience = _extract_experience_snippet(content_html)

        if not title:
            continue
        jobs.append({
            "title":               title,
            "institution":         expand_institution("EIB"),
            "department":          "",
            "location":            location,
            "deadline":            deadline,
            "posted":              published,
            "contract_type":       "",
            "who_can_apply":       "",
            "salary":              "",
            "grade":               "",
            "working_time":        "",
            "role_specialisation": "",
            "prerequisites":       "",
            "experience":          experience,
            "tags":                [],
            "description":         "",
            "entry_level":         infer_entry_level(title),
            "url":                 job_url,
            "source":              "EIB",
        })

    print(f"  EIB jobs found: {len(jobs)}")
    return jobs


# ─── OECD ─────────────────────────────────────────────────────────────────────

_OECD_BASE = "https://careers.smartrecruiters.com"
_OECD_PAGE = f"{_OECD_BASE}/OECD/oecd---en"


def _parse_oecd_html(html_text: str) -> list:
    """Extract job dicts from one SmartRecruiters HTML page."""
    soup = BeautifulSoup(html_text, "html.parser")
    jobs = []
    for li in soup.find_all("li", class_="opening-job"):
        a = li.find("a", href=True)
        if not a:
            continue
        h4 = li.find("h4", class_="job-title")
        if not h4:
            continue
        title = clean(h4.get_text())
        href = a["href"].strip()
        job_url = href if href.startswith("http") else _OECD_BASE + href

        loc_el = li.find("span", class_="margin--right--s")
        location = clean(loc_el.get_text()) if loc_el else "See posting"

        if not title:
            continue
        jobs.append({
            "title":               title,
            "institution":         expand_institution("OECD"),
            "department":          "",
            "location":            location,
            "deadline":            "See posting",
            "posted":              "",
            "contract_type":       "",
            "who_can_apply":       "",
            "salary":              "",
            "grade":               "",
            "working_time":        "",
            "role_specialisation": "",
            "prerequisites":       "",
            "experience":          "",
            "tags":                [],
            "description":         "",
            "entry_level":         infer_entry_level(title),
            "url":                 job_url,
            "source":              "OECD",
        })
    return jobs


def scrape_oecd() -> list:
    """Scrape OECD jobs from SmartRecruiters: main page + paginated API groups."""
    jobs: list = []
    seen_urls: set = set()

    # Main listing page
    try:
        r = SESSION.get(_OECD_PAGE, timeout=20)
        r.raise_for_status()
        for job in _parse_oecd_html(r.text):
            if job["url"] not in seen_urls:
                seen_urls.add(job["url"])
                jobs.append(job)
    except Exception as exc:
        print(f"  [!] OECD main page error: {exc}")

    # Paginated API endpoint for additional job groups
    try:
        api_url = f"{_OECD_PAGE}/api/groups"
        r = SESSION.get(api_url, timeout=20)
        r.raise_for_status()
        data = r.json()
        for group in data if isinstance(data, list) else data.get("groups", []):
            html_fragment = group.get("html", "")
            if not html_fragment:
                continue
            for job in _parse_oecd_html(html_fragment):
                if job["url"] not in seen_urls:
                    seen_urls.add(job["url"])
                    jobs.append(job)
    except Exception as exc:
        print(f"  [!] OECD API groups error: {exc}")

    print(f"  OECD jobs found: {len(jobs)}")
    return jobs


# ─── AIIB ─────────────────────────────────────────────────────────────────────

def scrape_aiib() -> list:
    """Scrape AIIB staff vacancies from their static JS data file."""
    js_url = (
        "https://www.aiib.org/en/opportunities/career/job-vacancies/staff"
        "/.content/index/current-jobs.js"
    )
    try:
        r = SESSION.get(js_url, timeout=20)
        r.raise_for_status()
        js = r.text
    except Exception as exc:
        print(f"  [!] AIIB fetch error: {exc}")
        return []

    def _field(n: int, key: str) -> str:
        m = re.search(rf'jobs\[{n}\]\["{re.escape(key)}"\]\s*=\s*"([^"]*)"', js)
        return m.group(1).strip() if m else ""

    # Discover how many entries exist by finding the highest index used
    indices = {int(m) for m in re.findall(r'jobs\[(\d+)\]', js)}
    if not indices:
        print("  [!] AIIB: no job entries found in JS file")
        return []

    jobs = []
    for n in sorted(indices):
        title = html.unescape(_field(n, "title"))
        path  = _field(n, "path")
        if not title or not path:
            continue
        job_url    = "https://www.aiib.org" + path
        deadline   = _field(n, "closing-date")
        dept       = _field(n, "department")
        location   = _field(n, "location") or "Beijing, China"
        raw_desc   = html.unescape(_field(n, "description"))
        experience = trunc(clean(raw_desc), 120) if raw_desc else ""

        jobs.append({
            "title":               title,
            "institution":         expand_institution("AIIB"),
            "department":          dept,
            "location":            location,
            "deadline":            deadline,
            "posted":              "",
            "contract_type":       "",
            "who_can_apply":       "",
            "salary":              "",
            "grade":               "",
            "working_time":        "",
            "role_specialisation": dept,
            "prerequisites":       "",
            "experience":          experience,
            "tags":                [],
            "description":         "",
            "entry_level":         infer_entry_level(title),
            "url":                 job_url,
            "source":              "AIIB",
        })

    print(f"  AIIB jobs found: {len(jobs)}")
    return jobs


# ─── ADB ──────────────────────────────────────────────────────────────────────

_ADB_BASE    = "https://www.adb.org"
_ADB_LIST    = f"{_ADB_BASE}/work-with-us/careers/current-opportunities"
_ADB_REF_RE  = re.compile(r"\s*/\s*\d+\s*$")


_ADB_HREF_RE = re.compile(r"^(https://www\.adb\.org)?/careers/\d+", re.I)


def _parse_adb_page(soup) -> list:
    """Extract job dicts from all job links on one ADB opportunities page."""
    jobs = []
    seen: set = set()

    for a in soup.find_all("a", href=_ADB_HREF_RE):
        href = a["href"].strip()
        job_url = href if href.startswith("http") else _ADB_BASE + href
        if job_url in seen:
            continue
        seen.add(job_url)

        title = clean(_ADB_REF_RE.sub("", a.get_text()))
        if not title:
            continue

        # Walk up to the nearest <tr> to find date cells, if available
        row = a.find_parent("tr")
        def _row_datetime(cls: str) -> str:
            if not row:
                return ""
            cell = row.find("td", class_=cls)
            if not cell:
                return ""
            t = cell.find("time")
            return t.get("datetime") or clean(t.get_text()) if t else ""

        posted   = _row_datetime("views-field-field-date-content")
        deadline = _row_datetime("views-field-field-date-closing")

        jobs.append({
            "title":               title,
            "institution":         expand_institution("ADB"),
            "department":          "",
            "location":            "Manila, Philippines",
            "deadline":            deadline,
            "posted":              posted,
            "contract_type":       "",
            "who_can_apply":       "",
            "salary":              "",
            "grade":               "",
            "working_time":        "",
            "role_specialisation": "",
            "prerequisites":       "",
            "experience":          "",
            "tags":                [],
            "description":         "",
            "entry_level":         infer_entry_level(title),
            "url":                 job_url,
            "source":              "ADB",
        })
    return jobs


_ADB_HEADERS = {
    "User-Agent":                "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    "Accept":                    "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language":           "en-US,en;q=0.5",
    "Accept-Encoding":           "gzip, deflate, br",
    "Connection":                "keep-alive",
    "Upgrade-Insecure-Requests": "1",
    "Referer":                   "https://www.adb.org/work-with-us/careers",
}


def _fetch_adb_page(page: int):
    """Fetch one ADB listing page: try rich headers first, fall back to Playwright."""
    url = f"{_ADB_LIST}?page={page}"
    try:
        r = requests.get(url, headers=_ADB_HEADERS, timeout=20, allow_redirects=True)
        if r.status_code == 403:
            raise requests.exceptions.HTTPError(response=r)
        r.raise_for_status()
        return BeautifulSoup(r.text, "html.parser")
    except requests.exceptions.HTTPError as exc:
        if exc.response is not None and exc.response.status_code == 403:
            print(f"    [ADB] 403 on page {page + 1}, retrying with Playwright…")
            raw_html = scrape_with_playwright(url, wait_ms=3000)
            return BeautifulSoup(raw_html, "html.parser")
        print(f"    [!] ADB HTTP error page {page + 1}: {exc}")
        return None
    except Exception as exc:
        print(f"    [!] ADB fetch error page {page + 1}: {exc}")
        return None


_ADB_QUAL_HEADING = re.compile(r"qualif|requirement|education|experience", re.I)


def _fetch_adb_detail(url: str) -> dict:
    """Fetch one ADB job page and extract grade, department, location, experience."""
    try:
        r = requests.get(url, headers=_ADB_HEADERS, timeout=20, allow_redirects=True)
        if r.status_code == 403:
            raise requests.exceptions.HTTPError(response=r)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
    except requests.exceptions.HTTPError as exc:
        if exc.response is not None and exc.response.status_code == 403:
            soup = BeautifulSoup(scrape_with_playwright(url, wait_ms=3000), "html.parser")
        else:
            return {}
    except Exception:
        return {}

    # Field extraction tries three HTML patterns in order:
    # 1. Drupal field__label / field__item divs
    # 2. <dt> / <dd> definition lists
    # 3. table <th> or <strong> next to a <td>
    def _get(soup, *labels) -> str:
        pats = [re.compile(lbl, re.I) for lbl in labels]

        for pat in pats:
            el = soup.find(class_=re.compile(r"field__label"), string=pat)
            if el:
                item = el.find_next_sibling(class_=re.compile(r"field__item"))
                if item:
                    return clean(item.get_text())

        for dt in soup.find_all("dt"):
            if any(p.search(dt.get_text()) for p in pats):
                dd = dt.find_next_sibling("dd")
                if dd:
                    return clean(dd.get_text())

        for cell in soup.find_all(["th", "td", "strong", "b"]):
            if any(p.search(cell.get_text()) for p in pats):
                nxt = cell.find_next_sibling("td")
                if not nxt:
                    row = cell.find_parent("tr")
                    nxt = row.find("td") if row else None
                if nxt and nxt is not cell:
                    return clean(nxt.get_text())

        return ""

    result: dict = {
        "grade":      _get(soup, "Position Level", "Grade", "Salary Level")[:40],
        "department": _get(soup, "Division", "Department", "Organizational Unit")[:80],
        "location":   _get(soup, r"\bLocation\b", "Duty Station")[:60],
    }

    # Qualifications / Requirements section: collect text after the matching heading
    for heading in soup.find_all(["h2", "h3", "h4", "strong", "b"]):
        if not _ADB_QUAL_HEADING.search(heading.get_text()):
            continue
        parts: list[str] = []
        for sib in heading.next_siblings:
            if getattr(sib, "name", None) in ("h2", "h3", "h4"):
                break
            text = clean(sib.get_text(" ") if hasattr(sib, "get_text") else str(sib))
            if text:
                parts.append(text)
            if sum(len(p) for p in parts) > 300:
                break
        full = clean(" ".join(parts))
        if len(full) > 20:
            result["experience"] = full[:200] + ("…" if len(full) > 200 else "")
            break

    return result


def scrape_adb() -> list:
    """Scrape ADB current opportunities with pagination, enriching each job with detail page data."""
    jobs: list = []
    page = 0

    while True:
        soup = _fetch_adb_page(page)
        if not soup:
            break
        page_jobs = _parse_adb_page(soup)
        if not page_jobs:
            break
        jobs.extend(page_jobs)
        print(f"    Page {page + 1}: {len(page_jobs)} jobs")
        page += 1
        time.sleep(1)

    print(f"  Fetching detail pages for {len(jobs)} ADB job(s)…")
    for job in jobs:
        detail = _fetch_adb_detail(job["url"])
        if detail.get("grade"):
            job["grade"]      = detail["grade"]
            job["entry_level"] = infer_entry_level(job["title"], detail["grade"])
        if detail.get("department"):
            job["department"]          = detail["department"]
            job["role_specialisation"] = detail["department"]
        if detail.get("location"):
            job["location"] = detail["location"]
        if detail.get("experience"):
            job["experience"] = detail["experience"]
        time.sleep(0.5)

    print(f"  ADB jobs found: {len(jobs)} across {page} page(s)")
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

        exp_html = ""
        experience = job.get("experience", "")
        if experience:
            exp_html = f'<div class="jex">{esc(experience)}</div>'

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
            f'{exp_html}'
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
@media(max-width:600px){{
  .fb{{padding:.75rem 1rem .6rem}}
  .fb-bot{{display:grid;grid-template-columns:1fr 1fr;gap:.4rem}}
  .fb select,#no-btn{{width:100%;box-sizing:border-box}}
  #inf{{grid-column:1/-1}}
  #cl{{grid-column:1/-1;margin-left:0;text-align:center}}
}}

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
.jin{{font-size:.83rem;font-weight:600;color:#2563eb;margin-bottom:.3rem}}
.jex{{font-size:.78rem;color:#6b7280;line-height:1.4;margin-bottom:.65rem;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}}

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

    HDR  = "background:#1a1a2e;border-radius:12px 12px 0 0;padding:28px 28px;text-align:center"
    BODY = "background:#ffffff;padding:24px 28px;border-left:1px solid #e8e8e8;border-right:1px solid #e8e8e8"
    FOOT = "background:#f8f6f2;border-radius:0 0 12px 12px;padding:22px 28px;text-align:center;border:1px solid #e8e8e8;border-top:none"
    EYE  = "margin:0 0 5px;font-size:10px;letter-spacing:2px;color:#94a3b8;text-transform:uppercase;font-family:Arial,sans-serif"
    H1   = "margin:0 0 5px;font-size:21px;color:#ffffff;font-family:Arial,sans-serif;font-weight:700"
    SUB  = "margin:0;font-size:13px;color:#94a3b8;font-family:Arial,sans-serif"
    CRD  = "margin-bottom:10px;background:#fffdf9;border:1px solid #ede8e0;border-radius:8px;padding:14px 16px"
    TTL  = "margin:0 0 3px;font-size:14px;font-weight:700;color:#1a1a2e;font-family:Arial,sans-serif;line-height:1.4"
    MTA  = "margin:0 0 9px;font-size:12px;color:#6b7280;font-family:Arial,sans-serif"
    ABT  = "display:inline-block;background:#003299;color:#ffffff;text-decoration:none;padding:5px 14px;border-radius:5px;font-size:11px;font-weight:700;font-family:Arial,sans-serif"
    RBT  = "display:inline-block;background:#1a1a2e;color:#ffffff;text-decoration:none;padding:12px 30px;border-radius:7px;font-size:14px;font-weight:700;font-family:Arial,sans-serif;letter-spacing:.3px"

    if has_new:
        shown    = new_jobs[:15]
        overflow = len(new_jobs) - 15
        cards    = []
        for j in shown:
            raw_title = j.get("title", "") or ""
            t   = esc(raw_title[:80] + ("…" if len(raw_title) > 80 else ""))
            inst = esc(j.get("institution", "") or "")
            dl   = j.get("deadline", "") or ""
            meta = inst + (f" · Deadline: {esc(dl)}" if dl else "")
            url  = esc(j.get("url", "#"))
            cards.append(
                f'<div style="{CRD}">'
                f'<p style="{TTL}">{t}</p>'
                f'<p style="{MTA}">{meta}</p>'
                f'<a href="{url}" style="{ABT}">Apply →</a>'
                f'</div>'
            )
        if overflow > 0:
            cards.append(
                f'<p style="margin:14px 0 0;font-size:13px;color:#6b7280;font-family:Arial,sans-serif;text-align:center">'
                f'…and <strong>{overflow}</strong> more in the full report</p>'
            )
        n      = len(new_jobs)
        header = (
            f'<p style="{EYE}">EU Job Tracker</p>'
            f'<h1 style="{H1}">{n} New EU Job{"s" if n != 1 else ""} Found</h1>'
            f'<p style="{SUB}">{esc(date_str)}</p>'
        )
        body = "".join(cards)
    else:
        header = (
            f'<p style="{EYE}">EU Job Tracker</p>'
            f'<h1 style="{H1}">Nothing New Today</h1>'
            f'<p style="{SUB}">{esc(date_str)}</p>'
        )
        body = (
            '<div style="background:#fdf8f3;border:1px solid #f0e6d8;border-radius:10px;padding:26px 22px;text-align:center">'
            '<p style="margin:0 0 10px;font-size:26px">🌟</p>'
            '<p style="margin:0 0 10px;font-size:15px;font-weight:700;color:#1a1a2e;font-family:Arial,sans-serif">Nothing new today, Alejandra</p>'
            '<p style="margin:0;font-size:14px;color:#555555;font-family:Georgia,serif;line-height:1.75">'
            "Nothing new on the EU job market today — but great things are on their way.<br>"
            "Your persistence is building something real. Keep going, you&#39;re doing amazing 🌟"
            "</p></div>"
        )

    return (
        f'<!DOCTYPE html><html><head><meta charset="UTF-8">'
        f'<meta name="viewport" content="width=device-width,initial-scale=1"></head>'
        f'<body style="margin:0;padding:0;background:#f4f1ec;font-family:Arial,sans-serif">'
        f'<div style="display:none;max-height:0;overflow:hidden;color:#f4f1ec">{esc(preheader)}</div>'
        f'<table width="100%" cellpadding="0" cellspacing="0" border="0" style="background:#f4f1ec">'
        f'<tr><td align="center" style="padding:28px 16px">'
        f'<table width="560" cellpadding="0" cellspacing="0" border="0" style="max-width:560px;width:100%">'
        f'<tr><td style="{HDR}">{header}</td></tr>'
        f'<tr><td style="{BODY}">{body}</td></tr>'
        f'<tr><td style="{FOOT}">'
        f'<a href="{REPORT_URL}" style="{RBT}">View Full Report →</a>'
        f'<p style="margin:12px 0 0;font-size:11px;color:#9ca3af;font-family:Arial,sans-serif">EU Job Tracker · automated daily scan</p>'
        f'</td></tr>'
        f'</table></td></tr></table>'
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
        subject   = f"[{len(new_jobs)}] New EU Jobs Found · {today}"
        preheader = ", ".join(j["title"] for j in new_jobs[:3])
    else:
        subject   = f"No New EU Jobs Today · {today}"
        preheader = "Nothing new today, but the full report is always available"

    body      = _build_email_html(new_jobs, has_new, preheader, today)
    body_bytes = len(body.encode("utf-8"))
    print(f"  Email HTML size: {body_bytes / 1024:.1f} KB ({body_bytes:,} bytes)")

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

    print("\nScraping EEAS (eeas.europa.eu/eeas/vacancies_en)...")
    eeas_jobs = scrape_eeas()
    print(f"  Raw jobs found: {len(eeas_jobs)}")

    print("\nScraping Bruegel (bruegel.org/careers)...")
    bruegel_jobs = scrape_bruegel()

    print("\nScraping EU Commission (eu-careers.europa.eu)...")
    ec_jobs = scrape_eu_commission()

    print("\nScraping EU Parliament (apply4ep.gestmax.eu)...")
    ep_jobs = scrape_eu_parliament()

    print("\nScraping EU Council (talents.coe.int)...")
    council_jobs = scrape_eu_council()

    print("\nScraping EIB (erecruitment.eib.org feed)...")
    eib_jobs = scrape_eib()

    print("\nScraping OECD (careers.smartrecruiters.com/OECD)...")
    oecd_jobs = scrape_oecd()

    print("\nScraping AIIB (aiib.org/en/opportunities/career)...")
    aiib_jobs = scrape_aiib()

    print("\nScraping ADB (adb.org/work-with-us/careers)...")
    adb_jobs = scrape_adb()

    jobs = process(ecb_jobs + eeas_jobs + bruegel_jobs + ec_jobs + ep_jobs + council_jobs + eib_jobs + oecd_jobs + aiib_jobs + adb_jobs, previous, keywords)
    save(jobs)

    print_summary(jobs, time.perf_counter() - t0)
    generate_report(jobs)
    send_email(jobs)


if __name__ == "__main__":
    main()
