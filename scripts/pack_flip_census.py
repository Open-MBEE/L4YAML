#!/usr/bin/env python3
"""The value-line PACK's punt surface, measured by ONE flip over the whole family (item 301).

`block_dispatch_deferred_stamp_nopack` is applied where a class-A `:` (the
explicit value of a `?` frame, at the frame's column) lands on a park whose
value-line pack is `Or.inr`.  The pack is one obligation carried through nine
`PendingNode` fields, the premises that restate it and the conclusions that
hand it on — every one with the same type tail, `… SLYamlStream sp_start sp_v)
∨ True` — and `frameChainUnion`, item 192's combinator, which states the same
alternative generically.  A one-field flip (§7, §9 of `BlockDeferralClasses`)
reads the field's own producers; the family's price is every producer that
hands ANY of them `Or.inr`, which only the whole flip reads.

The flip: every tail becomes `∨ False` in one patched tree, and `lake env lean`
runs to a fixpoint.  Each round, an error at `trivial`/`True.intro`/`⟨⟩` is a
DECLINE (the site is sorried and the round continues); an error at a
parenthesized group or a lone identifier is a RELAY from an unflipped source
(wrapped in `ofTrue_probe`, a probe lemma spliced in front of the first
declaration); any other shape stops the census, since a wrong wrap cascades.
`StreamAccum.lean` is restored byte-identical whatever happens.

Reads one line, pinned in `BlockDeferralClasses.expectedPackFlip`:

    PACK-FLIP sites=… decls=… rounds=… decline=… relay=… leaf=… uncond=…

`leaf` counts the declines of the shape `| Or.inr _ => Or.inr trivial` /
`else Or.inr trivial` — conditional on an INCOMING optional declining — and
`uncond` the bare ones; the two are the census's reading of transport versus
root.  `--tsv PATH` writes the per-site rows (round, line, column, kind,
declaration, message head, source line)."""
import argparse
import hashlib
import re
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
T = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
PIN = ROOT / "Tests/Guards/Proofs/BlockDeferralClasses.lean"
TAIL = "SLYamlStream sp_start sp_v) ∨ True"
FCU = "(∃ ns : List Nat, ∀ nv ∈ ns, P nv) ∨ True"
OPEN, CLOSE = "([{⟨", ")]}⟩"
LEAF = re.compile(r"^(\| .*=> Or\.inr trivial|else Or\.inr trivial|· exact Or\.inr trivial)")
ERR = re.compile(r"^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):(\d+): error: (.*)")


def check_pin(name, label, line):
    """The pin is a literal in the guard, checked from THIS side: nothing in
    Lean can re-derive a reading of a patched tree."""
    m = re.search(rf'def {name} : String :=\n  "([^"]*)"', PIN.read_text())
    if not m:
        print(f"{label} absent")
        return
    if m.group(1) == line:
        print(f"{label} agrees")
    else:
        print(f"{label} MOVED\n  got      {line}\n  expected {m.group(1)}")
        sys.exit(1)


def balanced_end(lines, ln, col):
    depth, i, j = 0, ln, col
    while True:
        s = lines[i]
        while j < len(s):
            if s.startswith("--", j):
                break
            if s[j] in OPEN:
                depth += 1
            elif s[j] in CLOSE:
                depth -= 1
                if depth == 0:
                    return i, j
            j += 1
        i += 1
        j = 0
        if i >= len(lines):
            raise SystemExit("unbalanced group")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tsv", type=Path, default=None)
    ap.add_argument("--max-rounds", type=int, default=40)
    args = ap.parse_args()
    md5 = lambda p: hashlib.md5(p.read_bytes()).hexdigest()
    m0 = md5(T)
    orig = T.read_text()
    orig_lines = orig.split("\n")
    L = orig.split("\n")
    flipped = [i for i, l in enumerate(L) if TAIL in l]
    for i in flipped:
        L[i] = L[i].replace(TAIL, "SLYamlStream sp_start sp_v) ∨ False")
    fcu = [i for i, l in enumerate(L) if FCU in l]
    for i in fcu:
        L[i] = L[i].replace(FCU, "(∃ ns : List Nat, ∀ nv ∈ ns, P nv) ∨ False")
    print(f"flipped {len(flipped)} tails + {len(fcu)} frameChainUnion lines")
    i0 = next(i for i, l in enumerate(L) if re.match(r"^(private )?(lemma|theorem|def|abbrev|structure|inductive) ", l))
    while L[i0 - 1].strip() != "":
        i0 -= 1
    probe = ["theorem ofTrue_probe {P : Prop} (h : P ∨ True) : P ∨ False :=",
             "  h.elim Or.inl (fun _ => Or.inr sorry)", ""]
    L = L[:i0] + probe + L[i0:]
    shift = len(probe)

    def oline(ln):
        return ln + 1 - shift if ln >= i0 + shift else ln + 1

    def odecl(n):
        d = "?"
        for k in range(min(n, len(orig_lines))):
            m = re.match(r"^(?:private )?(?:lemma|theorem|def|abbrev|structure|inductive) (\S+)", orig_lines[k])
            if m:
                d = m.group(1)
        return d

    census, seen, rounds = [], set(), 0
    bak = T.with_suffix(".lean.pack-flip.bak")
    shutil.copyfile(T, bak)
    t0 = time.time()
    stop = False
    try:
        for rnd in range(1, args.max_rounds + 1):
            rounds = rnd
            T.write_text("\n".join(L))
            r = subprocess.run(["lake", "env", "lean", str(T.relative_to(ROOT))], cwd=ROOT,
                               capture_output=True, text=True)
            errs = {}
            for l in (r.stdout + r.stderr).split("\n"):
                if (m := ERR.match(l)):
                    errs.setdefault((int(m.group(1)) - 1, int(m.group(2))), m.group(3)[:100])
            print(f"round {rnd}: {len(errs)} errors ({time.time() - t0:.0f}s)")
            if not errs:
                break
            for (ln, col), msg in sorted(errs.items(), reverse=True):
                s, o, text = L[ln], oline(ln), L[ln][col:]
                if (ln, col) in seen:
                    kind, stop = "UNHANDLED", True
                    print(f"  UNHANDLED recurrence at L{o}:{col}: {text[:60]!r} :: {msg}")
                elif any(text.startswith(t) for t in ("trivial", "True.intro", "⟨⟩")):
                    tok = next(t for t in ("trivial", "True.intro", "⟨⟩") if text.startswith(t))
                    L[ln] = s[:col] + "sorry" + s[col + len(tok):]
                    kind = "DECLINE"
                elif text.startswith("("):
                    el, ec = balanced_end(L, ln, col)
                    L[el] = L[el][:ec + 1] + ")" + L[el][ec + 1:]
                    L[ln] = s[:col] + "ofTrue_probe (" + s[col:]
                    kind = "RELAY"
                elif (m := re.match(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*", text)) and re.match(r"\s*($|[),⟩])", text[m.end():]):
                    L[ln] = s[:col] + "ofTrue_probe (" + m.group(0) + ")" + s[col + m.end():]
                    kind = "RELAY"
                else:
                    kind, stop = "UNHANDLED", True
                    print(f"  UNHANDLED shape at L{o}:{col}: {text[:70]!r} :: {msg}")
                seen.add((ln, col))
                census.append((rnd, o, col, kind, odecl(o), msg, orig_lines[o - 1].strip()[:110]))
            if stop:
                print("stopping on an unhandled site")
                break
        else:
            print("did not converge")
    finally:
        shutil.copyfile(bak, T)
        bak.unlink()
    assert md5(T) == m0, "StreamAccum NOT restored"
    if args.tsv:
        args.tsv.write_text("\n".join("\t".join(str(x) for x in c) for c in census) + "\n")
    by = Counter(c[4] for c in census)
    for d, n in sorted(by.items()):
        print(f"  {n:3d}  {d}")
    kinds = Counter(c[3] for c in census)
    leaf = sum(1 for c in census if c[3] == "DECLINE" and LEAF.match(c[6]))
    uncond = kinds["DECLINE"] - leaf
    line = (f"sites={len(census)} decls={len(by)} rounds={rounds} decline={kinds['DECLINE']} "
            f"relay={kinds['RELAY']} leaf={leaf} uncond={uncond}")
    if kinds["UNHANDLED"]:
        line += f" unhandled={kinds['UNHANDLED']}"
    print("PACK-FLIP " + line)
    check_pin("expectedPackFlip", "PACK-FLIP-PIN", line)


if __name__ == "__main__":
    main()
