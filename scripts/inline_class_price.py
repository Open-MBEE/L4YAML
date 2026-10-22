#!/usr/bin/env python3
"""The escape's INLINE class, measured at its feeders (item 286).

`block_dispatch_deferred_inline` is applied at two sites, and neither site
decides anything: each spends a STREAM its caller handed down
(`h_stream_fallback`), so the class's domain is the set of callers that hand a
stream rather than a refutation.  Item 184 measured that set as "the
implicit-key pack's punt" and item 264 copied the reading forward.  This script
re-derives it from the compiler.

`feeders` narrows the fallback to `False` in the three lemmas that take it
(`accum_block_on_closeThenBlock`, `…_pendingContent`, `…_pendingBlockContent`)
and turns both inline applications into `.elim`.  A caller that already
refutes the residue (`nodeStop_refutes_inline_residue`,
`docEnd_refutes_inline_residue`, `dispatch_refutes_sameLine`) still
elaborates; a caller that hands a stream breaks, ONCE, at the stream it hands.
So each error is one feeder, located at the park arm that pays it, and the
pass-through from `…_pendingContent` to `…_closeThenBlock` costs nothing
because both ends narrow together.

Elaborates StreamAccum alone (`lake env lean`) and restores it byte-identical,
md5-checked.

**`feeders` reads the tree as it stood at item 286.**  Item 287 retired the
fallback: `accum_block_on_closeThenBlock`'s `h_vslot` carries the caller's own
reading of an inline residue where the park holds no open slot, and each arm
that defers applies the escape itself.  So on a later tree `feeders` says so
and stops; `arms` reads the class's sites instead, by deleting the wrapper and
locating every application it then lacks.

`census` asks the RUNTIME what the class's reasons stand for, at every
yaml-test-suite case (all 351 sources) and a fixed list of hand-written
inputs.  A row is a park the `:` consumers read: the last real token is
content (a scalar, an alias or a closed flow collection) or a property, the
park is off column 0, the step to the next `:` crosses no break, and that `:`
is dispatched as a block VALUE indicator — `InlineResidue`'s own premise, read
off the scanner state.  Two readings per row:

* `nokey` — the park's saved key is not live on the park's line
  (`colon_fires_implicit_key`'s `¬ possible` arm, and its stale-key twin);
* `popped` — the park's OWN step popped the indent stack, and what the top
  entry is at the landing's column: a MAPPING level (a frame, wherever the
  cover holds), a SEQUENCE level, or no level at all.  That is what the pack
  producers' `w ∉ ks` exit stands for (`KeyPackPunt.dedent`'s until item 297).

The probe is written to `Scratch/` (gitignored), elaborated, and deleted.

Usage:
    python3 scripts/inline_class_price.py feeders   # item 286's tree
    python3 scripts/inline_class_price.py arms      # item 287 on
    python3 scripts/inline_class_price.py census
"""
import hashlib
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
REL = str(TARGET.relative_to(ROOT))
PIN = ROOT / "Tests/Guards/Proofs/BlockDeferralClasses.lean"

NARROWED = ["accum_block_on_closeThenBlock", "accum_block_on_pendingContent",
            "accum_block_on_pendingBlockContent"]

# The two inline applications, each anchored on its own first line and the
# fallback application under it.  Each is replaced by the `.elim` of the
# narrowed fallback, closing the parentheses the original closed.
SITES = {
    "closeThenBlock": (
        "      exact block_dispatch_deferred_inline sp_start sp_block_ctx sp_scan' s'",
        "      exact (h_stream_fallback h_res h_mid.2.2.1).elim"),
    "pendingBlockContent": (
        "      block_dispatch_deferred_inline sp_start sp_block_ctx sp_scan' s'",
        "      (h_stream_fallback h_res h_mid.2.2.1).elim)"),
}
SITE_LEN = 5    # the application's own lines, fallback and four premises


def md5(p):
    return hashlib.md5(p.read_bytes()).hexdigest()


def decl_starts(lines):
    out = []
    for i, l in enumerate(lines):
        m = re.match(r"^(?:private )?(?:lemma|theorem|def|abbrev|inductive|structure) (\S+)", l)
        if m:
            out.append((i, m.group(1)))
    return out


def enclosing(starts, i):
    d = "<file scope>"
    for j, name in starts:
        if j > i:
            break
        d = name
    return d


def arm_of(lines, i, decl_line):
    """The nearest `| pendingX …` case arm above line `i` inside its declaration."""
    for j in range(i, decl_line, -1):
        m = re.match(r"^  \| (\w+)\b", lines[j])
        if m:
            return m.group(1)
    return "-"


def narrow(lines):
    out = list(lines)
    starts = dict((name, i) for i, name in decl_starts(out))
    for decl in NARROWED:
        s = starts[decl]
        p = next(i for i in range(s, len(out)) if out[i].startswith("    (h_stream_fallback :"))
        q = next(i for i in range(p, p + 8) if out[i] == "      SLYamlStream sp_start sp_block_ctx)")
        out[q] = "      False)"
    for name, (head, repl) in SITES.items():
        hits = [i for i, l in enumerate(out) if l == head]
        assert len(hits) == 1, (name, hits)
        i = hits[0]
        assert "(h_stream_fallback h_res h_mid.2.2.1)" in out[i + 1], (name, out[i + 1])
        assert out[i + SITE_LEN - 1].strip().startswith("(nic0_of_block_dispatch"), (name, out[i + 4])
        tail = out[i + SITE_LEN - 1].rstrip()
        # the closing parentheses the application's last line carried beyond its own
        extra = len(tail) - len(tail.rstrip(")")) - 1
        assert extra == (1 if name == "pendingBlockContent" else 0), (name, tail)
        out[i:i + SITE_LEN] = [repl]
    return out


def run(lines):
    before = md5(TARGET)
    orig = TARGET.read_bytes()
    t0 = time.time()
    try:
        TARGET.write_text("\n".join(lines))
        proc = subprocess.run(["lake", "env", "lean", REL], cwd=ROOT,
                              capture_output=True, text=True)
    finally:
        TARGET.write_bytes(orig)
    after = md5(TARGET)
    print(f"md5 StreamAccum.lean  before {before}  after {after}  "
          f"{'==' if before == after else 'DIFFERS'}   ({time.time() - t0:.0f}s)")
    assert before == after
    return proc.stdout + proc.stderr


def feeders():
    src = TARGET.read_text().split("\n")
    if not any(l.startswith("    (h_stream_fallback :") for l in src):
        print("feeders: `h_stream_fallback` retired at item 287 -- "
              "`arms` reads the class's sites on this tree")
        return
    patched = narrow(src)
    body = run(patched)
    pat = re.compile(rf"^{re.escape(REL)}:(\d+):(\d+): error: (.*)$")
    rows = []
    starts = decl_starts(patched)
    for l in body.split("\n"):
        m = pat.match(l)
        if m:
            ln, col, msg = int(m.group(1)), int(m.group(2)), m.group(3)
            i = ln - 1
            d = enclosing(starts, i)
            dl = max(j for j, n in starts if j <= i)
            rows.append((d, arm_of(patched, i, dl), ln, col, msg, patched[i].strip()))
    by = {}
    for r in rows:
        by.setdefault(r[0], []).append(r)
    print(f"\n=== feeders: {len(rows)} errors / {len(by)} declarations ===")
    for d, rs in sorted(by.items(), key=lambda kv: kv[1][0][2]):
        own = " (NARROWED -- its own body)" if d in NARROWED else ""
        print(f"  {len(rs):3d}  {d}{own}")
        for _, arm, ln, col, msg, text in rs:
            print(f"         L{ln}:{col:<4} arm {arm:<20} {msg[:60]}")
            print(f"                     {text[:90]}")
    arms = sorted({(d, a) for d, a, *_ in rows if d not in NARROWED})
    other = [l for l in body.split("\n") if "error" in l and not pat.match(l)]
    if other:
        print("  (other error lines:", len(other), ")")
        for l in other[:10]:
            print("   ", l[:160])
    line = (f"errors={len(rows)} decls={len(by)} feeders="
            + ",".join(f"{d}/{a}" for d, a in arms))
    print("INLINE-FEEDERS " + line)
    check_pin("expectedInlineFeeders", "INLINE-FEEDERS-PIN", line)


def check_pin(name, label, line):
    """The pin is a literal in the guard, checked from THIS side: nothing in
    Lean can re-derive a reading of a patched tree or of a corpus run."""
    m = re.search(rf'def {name} : String :=\n  "([^"]*)"', PIN.read_text())
    if not m:
        print(f"{label} absent")
        return
    if m.group(1) == line:
        print(f"{label} agrees")
    else:
        print(f"{label} MOVED\n  got      {line}\n  expected {m.group(1)}")
        sys.exit(1)


# ---------------------------------------------------------------------------
# `arms` mode (item 287): the class's sites, by deleting the wrapper.

WRAPPER = "block_dispatch_deferred_inline"


def wrapper_span(lines):
    """The wrapper's declaration with its docstring, as `(first, last+1)`."""
    head = [i for i, l in enumerate(lines) if l == f"lemma {WRAPPER}"]
    assert len(head) == 1, head
    i = head[0]
    end = i + 1
    while end < len(lines) and not (lines[end] and not lines[end][0].isspace()):
        end += 1
    start = i
    if lines[start - 1].rstrip().endswith("-/"):
        start -= 1
        while not lines[start].startswith("/--"):
            start -= 1
    return start, end


def arm_label(lines, i, decl_line):
    """The case arm an application stands in: its own `| reason =>`, the
    nearest `| pendingX` park arm above it, or the `by_cases` it negates."""
    # a punt REASON's own arm, written on the application's line; any other
    # `| …` there (a `match` on the slot, say) is not the arm it stands in
    m = re.match(r"^\s*\| (\w+)", lines[i])
    if m and m.group(1) in ("tab", "implicitValue", "markerLine", "noKeyContext"):  # item 297: no `dedent`; item 300: `markerLine`
        return m.group(1)
    ind = len(lines[i]) - len(lines[i].lstrip())
    for j in range(i - 1, decl_line, -1):
        t = lines[j]
        if not t.strip() or t.strip().startswith("--"):
            continue
        tind = len(t) - len(t.lstrip())
        m = re.match(r"^  \| (pending\w+)", t)
        if m:
            return m.group(1)
        if tind == ind:
            m = re.match(r"^\s*by_cases (\w+)", t)
            if m:
                return "¬" + m.group(1)
    return "-"


def arms():
    src = TARGET.read_text().split("\n")
    a, b = wrapper_span(src)
    patched = src[:a] + ["-- WRAPPER DELETED (scripts/inline_class_price.py arms)"] * (b - a) + src[b:]
    body = run(patched)
    pat = re.compile(rf"^{re.escape(REL)}:(\d+):(\d+): error(?:\([\w.]+\))?: (.*)$")
    starts = decl_starts(src)
    rows, other = [], []
    for l in body.split("\n"):
        m = pat.match(l)
        if not m:
            continue
        ln, msg = int(m.group(1)), m.group(3)
        if WRAPPER not in msg:
            other.append(l)
            continue
        i = ln - 1
        d = enclosing(starts, i)
        dl = max(j for j, n in starts if j <= i)
        rows.append((d, arm_label(src, i, dl), ln))
    by = {}
    for d, arm, ln in rows:
        by.setdefault(d, []).append((arm, ln))
    print(f"\n=== arms: {len(rows)} applications / {len(by)} declarations ===")
    for d, rs in sorted(by.items()):
        print(f"  {len(rs):3d}  {d}")
        for arm, ln in rs:
            print(f"         L{ln:<6} {arm}")
    if other:
        print(f"  ({len(other)} other errors -- the deletion broke more than the applications)")
        for l in other[:10]:
            print("   ", l[:180])
    line = (f"apps={len(rows)} decls={len(by)} arms="
            + ",".join(f"{d}/{arm}" for d, arm, _ in sorted(rows)))
    print("INLINE-ARMS " + line)
    check_pin("expectedInlineArms", "INLINE-ARMS-PIN", line)


# ---------------------------------------------------------------------------
# `census` mode: the runtime under the class's reasons.

PROBE = ROOT / "Scratch/InlineClassCensus.lean"

# Hand-written rows: the families BlockDeferralClasses §3 pins one by one.
CANDIDATES = [
    "\"a\" b : c\n", "&x a\n*x : b\n", "a: *x : b\n", "[a] b : c\n", "--- a : b\n",
    "- a : b\n", "a: b : c\n", "? a : b\n", "? a\n: b : c\n", "\"a\nb\" : c\n",
    "a\n b : c\n", "- !t a : b\n", "&x a : b\n", "&p : v\n", "!t : v\n", "k: &p : 1\n",
    "- &p : v\n", "? &p : v\n", "k:\n  :\n&p : 2\n", "&a !t : v\n", "k:\n  :\nb: 2\n",
    "- a:\n    b:\n  c: 1\n", "a:\n  b:\n    c:\nd: 1\n", "[a] : b\n", "{a: 1} : b\n",
    "- [a] : b\n", "k: [a] : b\n", "'a' : b\n", "\"a\" : b\n", "a\t: b\n", "*x : b\n",
]

PROGRAM = r"""import Tests.SuiteRunner.Meta
import L4YAML.Scanner.IndexedDispatch

open L4YAML L4YAML.Scanner Tests.SuiteRunner

def trace (input : String) : Array ScannerState × Bool := Id.run do
  let mut s := (ScannerState.mk' input).emit .streamStart
  let mut out : Array ScannerState := #[s]
  for _ in [0:400] do
    match scanNextToken s with
    | .ok (some s') => s := s'; out := out.push s'
    | .ok none =>
      match scanLoop_checkDanglingNode s, scanLoop_checkFlowValueIndent s with
      | .ok (), .ok () => return (out, true)
      | _, _ => return (out, false)
    | .error _ => return (out, false)
  return (out, false)

def kindOf : Option YamlToken → String
  | some (.scalar _ _) | some (.alias _) | some .flowSequenceEnd | some .flowMappingEnd => "content"
  | some (.anchor _) | some (.tag _ _) => "props"
  | _ => "other"

def landing (sc0 : ScannerState) : String :=
  match scanNextToken_preprocess sc0 with
  | .ok (some (s0, _)) =>
    if s0.indents.size < sc0.indents.size then
      match s0.indents.back? with
      | some e =>
        if e.column == (s0.col : Int) then
          (if e.isSequence then "onto-seq" else "onto-map")
        else "off-level"
      | none => "off-level"
    else "no-pop"
  | _ => "?"

def rows (tag input : String) : Array String := Id.run do
  let (ss, ok) := trace input
  let mut out := #[]
  for i in [1:ss.size] do
    let sc := ss[i]!
    match scanNextToken_preprocess sc with
    | .ok (some (s_prep, ':')) =>
      let s_dis := if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true } else s_prep
      let disp := match scanNextToken_dispatchBlockIndicators s_dis ':' with
        | .ok (some _) => true | _ => false
      let k := kindOf (lastRealTokenVal? sc.tokens)
      if !s_prep.inFlow && s_prep.line == sc.line && sc.col != 0 && disp && k != "other" then
        let live := sc.simpleKey.possible && sc.simpleKey.pos.line == sc.line
        out := out.push s!"ROW\t{k}\tacc={ok}\tlive={live}\t{landing ss[i-1]!}\t{tag}\t{repr input}"
    | _ => pure ()
  return out

def candidates : List String := CANDIDATES_HERE

#eval show IO Unit from do
  let dir : System.FilePath := "yaml-test-suite/src"
  let mut n := 0
  for e in ((← dir.readDir).qsort (fun a b => a.fileName < b.fileName)) do
    if e.path.extension == some "yaml" then
      n := n + 1
      let id := e.path.fileStem.getD "?"
      let mut j := 0
      for tc in parseTestFile id (← IO.FS.readFile e.path) do
        for r in rows s!"{id}#{j}" (unescapeTestYaml tc.yaml) do IO.println r
        j := j + 1
  IO.println s!"SOURCES {n}"
  for c in candidates do
    for r in rows "cand" c do IO.println r
"""


def lean_str(t):
    return '"' + t.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'


def census():
    prog = PROGRAM.replace("CANDIDATES_HERE", "[" + ", ".join(lean_str(c) for c in CANDIDATES) + "]")
    PROBE.parent.mkdir(exist_ok=True)
    PROBE.write_text(prog)
    t0 = time.time()
    try:
        proc = subprocess.run(["lake", "env", "lean", str(PROBE.relative_to(ROOT))], cwd=ROOT,
                              capture_output=True, text=True)
    finally:
        PROBE.unlink()
    body = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print(body[:3000]); sys.exit(f"census probe failed ({proc.returncode})")
    rows = [l.split("\t") for l in body.split("\n") if l.startswith("ROW\t")]
    src = next(int(l.split()[1]) for l in body.split("\n") if l.startswith("SOURCES "))
    acc = [r for r in rows if r[2] == "acc=true"]
    nokey = [r for r in acc if r[3] == "live=false"]
    popped = [r for r in acc if r[4] != "no-pop"]
    by = {}
    for r in popped:
        by[r[4]] = by.get(r[4], 0) + 1
    print(f"sources {src}, candidates {len(CANDIDATES)}  ({time.time() - t0:.0f}s)")
    for kind in ("content", "props"):
        ks = [r for r in rows if r[1] == kind]
        ka = [r for r in ks if r[2] == "acc=true"]
        print(f"  {kind:<8} rows {len(ks):4d}   accepted {len(ka):4d}   refused {len(ks) - len(ka):4d}")
    print(f"  accepted with no live key on the park's line: {len(nokey)}")
    for r in nokey:
        print("     ", r[5], r[6][:100])
    print(f"  accepted whose own landing popped: {len(popped)}  "
          + "  ".join(f"{k}={v}" for k, v in sorted(by.items())))
    for r in popped:
        if r[4] != "onto-map":
            print("     ", r[4], r[5], r[6][:100])
    line = (f"rows={len(rows)} accepted={len(acc)} nokey={len(nokey)} popped={len(popped)} "
            f"onto-map={by.get('onto-map', 0)} onto-seq={by.get('onto-seq', 0)} "
            f"off-level={by.get('off-level', 0)}")
    print("INLINE-CENSUS " + line)
    check_pin("expectedInlineCensus", "INLINE-CENSUS-PIN", line)


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "feeders"
    if which == "feeders":
        feeders()
    elif which == "arms":
        arms()
    elif which == "census":
        census()
    else:
        sys.exit("usage: inline_class_price.py feeders|arms|census")
