#!/usr/bin/env python3
"""Compare the four suiterunner backends across every limits preset.

The conformance claim this repo publishes is that the Lean parser, the C shared
library, the Python bindings and the Rust crate accept and reject *exactly* the
same yaml-test-suite cases.  That is only an observation if something checks it,
so this runs all four backends under all five presets and fails unless every
preset's four readings are identical.

    cross-lang-compare.py <results-dir>

Writes `<results-dir>/cross-lang-results.json` and exits 1 on any mismatch or
missing TOTAL line.  Needs `.lake/build/bin/suiterunner` built, the C artifacts
at `ffi/out/` (the `c` backend) and `L4YAML_LIB`/`LD_LIBRARY_PATH` pointing at
them (the `python` backend).

Shared by `.github/workflows/test-coverage.yml` and `scripts/generate-all.sh`
so the local run and CI score the same way — two copies of this would be two
producers of one number.
"""

import json
import pathlib
import subprocess
import sys

BACKENDS = ["lean", "c", "python", "rust"]
PRESETS = ["unlimited", "default", "strict", "permissive", "safe_tags"]
SUITERUNNER = ".lake/build/bin/suiterunner"


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <results-dir>", file=sys.stderr)
        return 2
    results_dir = pathlib.Path(sys.argv[1])

    results: dict[tuple[str, str], tuple[int, int, int, int]] = {}
    all_match = True

    for preset in PRESETS:
        for backend in BACKENDS:
            cmd = [SUITERUNNER, "--backend", backend, "--limits", preset]
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
            output = proc.stdout + proc.stderr
            for line in output.splitlines():
                if "TOTAL:" in line:
                    parts = line.split()
                    p, f, s, t = (
                        int(parts[1]),
                        int(parts[3]),
                        int(parts[5]),
                        int(parts[7].strip("()")),
                    )
                    results[(backend, preset)] = (p, f, s, t)
                    break
            else:
                print(f"ERROR: no TOTAL line for {backend}/{preset}", file=sys.stderr)
                results[(backend, preset)] = (0, 0, 0, 0)
                all_match = False

        vals = [results[(b, preset)] for b in BACKENDS]
        if len(set(vals)) != 1:
            print(f"MISMATCH for preset '{preset}': {dict(zip(BACKENDS, vals))}")
            all_match = False
        else:
            p, f, s, t = vals[0]
            print(
                f"{preset:12s}: {p} passed, {f} failed, {s} skipped "
                f"({t} total) — all 4 backends identical"
            )

    print()
    if all_match:
        print("✓ All backends produce identical results for every preset")
    else:
        print("✗ Backend mismatch detected!")
        return 1

    json_data: dict[str, dict[str, dict[str, int]]] = {}
    for (backend, preset), (p, f, s, t) in results.items():
        json_data.setdefault(preset, {})[backend] = {
            "passed": p,
            "failed": f,
            "skipped": s,
            "total": t,
        }
    (results_dir / "cross-lang-results.json").write_text(json.dumps(json_data, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
