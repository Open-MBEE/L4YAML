#!/usr/bin/env python3
"""Navigate DOCS.md without paging it.

DOCS.md is a 45k-line consolidated history; the Row 12 closure log alone holds
~290 dated items.  This prints the slice an agent needs:

    docs_nav.py toc                   top-level sections with line numbers
    docs_nav.py items [--since N] [--last K]
                                      one line per closure-log item
    docs_nav.py item N [--lines]      the full entry for item N (N may carry a suffix: 67a)
    docs_nav.py next [N]              the NEXT (mandate) paragraph of item N
                                      (default: the latest item)
    docs_nav.py remaining             the "REMAINING, in order" dependency section (dated; see `steps`)
    docs_nav.py steps                 the Row 12 six-step table and next-actions table
    docs_nav.py grep REGEX [-i]       items whose body matches, with hit counts
    docs_nav.py section PREFIX        a `## ` section by heading prefix

Read-only; stdlib only.  Line numbers are 1-based and match `sed -n`.
"""

from __future__ import annotations

import argparse
import re
import signal
import sys
from dataclasses import dataclass
from pathlib import Path

DOCS = Path(__file__).resolve().parent.parent / "DOCS.md"

ITEM_RE = re.compile(r"^### Item (\d+)([a-z]?) \((\d{4}-\d{2}-\d{2})\)\s*$")
H2_RE = re.compile(r"^## (?!§)(.+?)\s*$")
NEXT_RE = re.compile(r"^\*\*NEXT\b")
MANDATE_RE = re.compile(r"^\*\*The mandate\b")
REMAINING_HEADING = "### REMAINING, in order"
NEXT_ACTIONS_HEADING = "### Next actions, in order"
SIX_STEPS_HEADING = "#### Row 12 — the six steps that finish it"


@dataclass
class Item:
    number: int
    suffix: str  # "" or a letter, as in "Item 67a"
    date: str
    start: int  # 1-based line of the heading
    end: int  # exclusive, 1-based

    @property
    def label(self) -> str:
        return f"{self.number}{self.suffix}"

    def body(self, lines: list[str]) -> list[str]:
        return lines[self.start - 1 : self.end - 1]


def load() -> list[str]:
    return DOCS.read_text(encoding="utf-8").splitlines()


def find_items(lines: list[str]) -> list[Item]:
    items: list[Item] = []
    for i, line in enumerate(lines, 1):
        m = ITEM_RE.match(line)
        if m:
            items.append(Item(int(m.group(1)), m.group(2), m.group(3), i, len(lines) + 1))
    for cur, nxt in zip(items, items[1:]):
        cur.end = nxt.start
    for it in items:
        for i in range(it.start, it.end - 1):
            if lines[i] == REMAINING_HEADING or H2_RE.match(lines[i]):
                it.end = i + 1
                break
    return items


def headline(lines: list[str], item: Item, width: int) -> str:
    """First sentence of the item's opening bold paragraph."""
    para: list[str] = []
    for line in item.body(lines)[1:]:
        if not line.strip():
            if para:
                break
            continue
        para.append(line.strip())
    text = " ".join(para)
    m = re.match(r"\*\*(.+?)\*\*", text)
    text = m.group(1) if m else text
    text = re.sub(r"\s+", " ", text)
    return text if len(text) <= width else text[: width - 1] + "…"


def paragraphs(block: list[str]) -> list[list[str]]:
    out: list[list[str]] = []
    cur: list[str] = []
    for line in block:
        if line.strip():
            cur.append(line)
        elif cur:
            out.append(cur)
            cur = []
    if cur:
        out.append(cur)
    return out


def next_paragraph(lines: list[str], item: Item) -> list[str] | None:
    body = item.body(lines)
    for para in paragraphs(body):
        if NEXT_RE.match(para[0]):
            return para
    return None


def emit(lines: list[str], start: int, end: int, numbered: bool) -> None:
    for i in range(start, end):
        line = lines[i - 1]
        print(f"{i}:{line}" if numbered else line)


def lookup(items: list[Item], label: str) -> Item:
    for it in items:
        if it.label == label:
            return it
    sys.exit(f"no item {label} (have {items[0].label}–{items[-1].label})")


def heading_block(lines: list[str], heading: str, stop) -> tuple[int, int]:
    """[start, end) of the block beginning at the exact `heading` line."""
    try:
        start = lines.index(heading) + 1
    except ValueError:
        sys.exit(f"heading not found: {heading!r}")
    end = len(lines) + 1
    for i in range(start, len(lines)):
        if stop(lines[i]):
            end = i + 1
            break
    return start, end


def cmd_toc(lines: list[str], _args) -> None:
    for i, line in enumerate(lines, 1):
        if H2_RE.match(line) or line in (
            REMAINING_HEADING,
            NEXT_ACTIONS_HEADING,
            SIX_STEPS_HEADING,
        ):
            print(f"{i:6d}  {line}")
    items = find_items(lines)
    if items:
        print(
            f"        ({len(items)} closure-log items, "
            f"{items[0].label}–{items[-1].label}, lines {items[0].start}–{items[-1].end - 1})"
        )


def cmd_items(lines: list[str], args) -> None:
    items = find_items(lines)
    if args.since is not None:
        items = [it for it in items if it.number >= args.since]
    if args.last is not None:
        items = items[-args.last :]
    for it in items:
        print(f"{it.label:>5}  {it.date}  L{it.start:<6d} {headline(lines, it, args.width)}")


def cmd_item(lines: list[str], args) -> None:
    it = lookup(find_items(lines), args.n)
    emit(lines, it.start, it.end, args.lines)


def mandate_paragraph(lines: list[str], item: Item) -> list[str] | None:
    for para in paragraphs(item.body(lines)):
        if MANDATE_RE.match(para[0]):
            return para
    return None


def cmd_next(lines: list[str], args) -> None:
    items = find_items(lines)
    it = items[-1] if args.n is None else lookup(items, args.n)
    print(f"# item {it.label} ({it.date}), DOCS.md:{it.start}")
    para = next_paragraph(lines, it)
    if para is not None:
        print("\n".join(para))
        return
    print(f"(item {it.label} records no **NEXT —** paragraph; older items state what came next in prose)")
    idx = items.index(it)
    if idx + 1 < len(items):
        follower = items[idx + 1]
        mandate = mandate_paragraph(lines, follower)
        if mandate is not None:
            print(f"# what item {follower.label} ({follower.date}, DOCS.md:{follower.start}) took as its mandate:")
            print("\n".join(mandate))
            return
        print(f"# read `item {it.label}` and the opening of `item {follower.label}` (DOCS.md:{follower.start})")
    else:
        print(f"# read `item {it.label}`")


def cmd_remaining(lines: list[str], args) -> None:
    start, end = heading_block(lines, REMAINING_HEADING, lambda l: ITEM_RE.match(l) or H2_RE.match(l))
    items = find_items(lines)
    before = [it for it in items if it.start < start]
    after = [it for it in items if it.start > start]
    where = f"DOCS.md:{start}"
    if before and after:
        where += f", written between items {before[-1].label} and {after[0].label} ({after[0].date})"
    print(f"# {where}.  Items after it may have moved its rows; the per-step state is `steps`,")
    print(f"# the latest mandate is `next` (item {items[-1].label}).")
    emit(lines, start, end, args.lines)


def cmd_steps(lines: list[str], args) -> None:
    def table_end(l: str) -> bool:
        return l.startswith("#")

    for heading in (NEXT_ACTIONS_HEADING, SIX_STEPS_HEADING):
        start, end = heading_block(lines, heading, table_end)
        emit(lines, start, end, args.lines)


def cmd_grep(lines: list[str], args) -> None:
    rx = re.compile(args.regex, re.IGNORECASE if args.ignore_case else 0)
    total = 0
    for it in find_items(lines):
        hits = sum(1 for l in it.body(lines) if rx.search(l))
        if hits:
            total += hits
            print(f"{it.label:>5}  {it.date}  L{it.start:<6d} {hits:3d}  {headline(lines, it, args.width)}")
    print(f"# {total} matching lines", file=sys.stderr)


def cmd_section(lines: list[str], args) -> None:
    want = args.prefix.lower()
    for i, line in enumerate(lines, 1):
        m = H2_RE.match(line)
        if m and m.group(1).lower().startswith(want):
            end = len(lines) + 1
            for j in range(i, len(lines)):
                if H2_RE.match(lines[j]):
                    end = j + 1
                    break
            emit(lines, i, end, args.lines)
            return
    sys.exit(f"no `## ` section starts with {args.prefix!r}; see `toc`")


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    def add_lines(sp):
        sp.add_argument("--lines", action="store_true", help="prefix each line with its DOCS.md line number")

    def add_width(sp):
        sp.add_argument("--width", type=int, default=100, help="headline truncation width")

    sub.add_parser("toc").set_defaults(fn=cmd_toc)
    sp = sub.add_parser("items")
    sp.add_argument("--since", type=int)
    sp.add_argument("--last", type=int)
    add_width(sp)
    sp.set_defaults(fn=cmd_items)
    sp = sub.add_parser("item")
    sp.add_argument("n", help="item number, e.g. 264 or 67a")
    add_lines(sp)
    sp.set_defaults(fn=cmd_item)
    sp = sub.add_parser("next")
    sp.add_argument("n", nargs="?", help="item number (default: latest)")
    sp.set_defaults(fn=cmd_next)
    sp = sub.add_parser("remaining")
    add_lines(sp)
    sp.set_defaults(fn=cmd_remaining)
    sp = sub.add_parser("steps")
    add_lines(sp)
    sp.set_defaults(fn=cmd_steps)
    sp = sub.add_parser("grep")
    sp.add_argument("regex")
    sp.add_argument("-i", "--ignore-case", action="store_true")
    add_width(sp)
    sp.set_defaults(fn=cmd_grep)
    sp = sub.add_parser("section")
    sp.add_argument("prefix")
    add_lines(sp)
    sp.set_defaults(fn=cmd_section)

    args = p.parse_args(argv)
    args.fn(load(), args)


if __name__ == "__main__":
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
