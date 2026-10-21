#!/usr/bin/env python3
"""Unified YAML-processor scorer over the yaml-test-suite *data* form.

Runs each processor's `-event` / `-json` tester (reading YAML on stdin) over
every test and scores it exactly the way http://matrix.yaml.info does:

  * error tests (dir has an `error` file): correct iff the parser errors (rc!=0)
  * valid  tests (event axis): correct iff emitted events == test.event
  * valid  tests (json  axis): correct iff emitted JSON == in.json (structural)

All processors — L4YAML's native binary and every docker tester — go through the
identical code path, so the numbers are apples-to-apples.

A tester the harness cannot start (wrong path, no `docker`, missing container or
tester) and an unusable `in.json` oracle score `harness-error`, never
`err-ok`/`reject`/`diff`, and the run exits nonzero.
"""
import os, sys, glob, json, argparse, subprocess
from concurrent.futures import ThreadPoolExecutor

def leaf_dirs(data):
    # `tags/` and `name/` are symlink index dirs in the data branch — skip them
    return sorted(os.path.dirname(p) for p in glob.glob(data + '/**/in.yaml', recursive=True)
                  if '/tags/' not in p and '/name/' not in p)

# ---- event normalization -----------------------------------------------------
def norm_events(text):
    lines = [l.rstrip('\r') for l in text.split('\n')]
    while lines and lines[-1] == '':
        lines.pop()
    return lines

# ---- json normalization (handles concatenated multi-document streams) --------
def parse_json_stream(text):
    dec = json.JSONDecoder()
    vals, i, n = [], 0, len(text)
    while i < n:
        while i < n and text[i] in ' \t\r\n':
            i += 1
        if i >= n:
            break
        obj, end = dec.raw_decode(text, i)
        vals.append(obj)
        i = end
    return vals

TIMEOUT_RC = 124   # sentinel exit code for a tester killed by the harness's timeout

_harness_errors_reported = set()

def harness_error(msg):
    """Record a harness (not processor) failure once on stderr; returns the category."""
    if msg not in _harness_errors_reported:
        _harness_errors_reported.add(msg)
        print(f"# harness error: {msg}", file=sys.stderr)
    return 'harness-error'

def run(cmd, stdin_bytes, timeout):
    """Return (rc, stdout); rc is None when the tester could not be started at all."""
    try:
        p = subprocess.run(cmd, input=stdin_bytes,
                           stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                           timeout=timeout)
        return p.returncode, p.stdout
    except subprocess.TimeoutExpired:
        return TIMEOUT_RC, b''
    except OSError as e:
        harness_error(f"cannot run {cmd[0]}: {e}")
        return None, b''

def tester_available(cmd):
    """Preflight: None if the tester can be started, else the reason it cannot.

    `docker exec` exits nonzero on its own when the container is missing or
    stopped (rc 1) or the tester is not in the image (rc 127); scored blind
    those would pass for parser rejections, so probe once before scoring."""
    if cmd[0] != 'docker':
        return None if os.access(cmd[0], os.X_OK) else f"{cmd[0]} is not an executable file"
    container, tester = cmd[3], cmd[4]   # cmd = docker exec -i <container> <tester>
    probe = ['docker', 'exec', container, 'sh', '-c', f'command -v {tester}']
    try:
        p = subprocess.run(probe, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as e:
        return f"cannot run docker: {e}"
    if p.returncode != 0:
        err = p.stderr.decode('utf-8', 'replace').strip()
        return f"{tester} not runnable in container {container}: {err or f'rc={p.returncode}'}"
    return None

def rc_category(rc, is_err):
    """Category decided by the exit code alone; None when the output must be compared."""
    if rc is None:
        return 'harness-error'   # checked first so a broken harness never scores err-ok
    if is_err:
        return 'err-ok' if rc != 0 else 'err-miss'
    if rc == TIMEOUT_RC:
        return 'timeout'
    if rc != 0:
        return 'reject'
    return None

def test_id(d):
    parts = d.rstrip('/').split(os.sep)
    return '/'.join(parts[-2:]) if parts[-1].isdigit() else parts[-1]

def no_oracle(d, axis):
    """A json-axis test without in.json has nothing to compare against: `skip`."""
    return axis == 'json' and not os.path.exists(d + '/in.json')

def score_one(cmd, d, axis, timeout):
    """Return (category, testid). category in the axis vocabulary."""
    tid = test_id(d)
    if no_oracle(d, axis):
        return ('skip', tid)
    inp = open(d + '/in.yaml', 'rb').read()
    is_err = os.path.exists(d + '/error')
    if axis == 'event':
        rc, out = run(cmd, inp, timeout)
        cat = rc_category(rc, is_err)
        if cat:
            return (cat, tid)
        exp = open(d + '/test.event', encoding='utf-8').read()
        got = out.decode('utf-8', 'replace')
        return ('pass' if norm_events(got) == norm_events(exp) else 'diff', tid)
    else:  # json
        rc, out = run(cmd, inp, timeout)
        # a few error tests carry a stale in.json (9MQT/01, DK95/01,
        # DK95/06); correct behavior is still to reject the input
        cat = rc_category(rc, is_err)
        if cat:
            return (cat, tid)
        try:
            exp = parse_json_stream(open(d + '/in.json', encoding='utf-8').read())
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as e:
            # the oracle is test data, so a bad one is the harness's fault
            return (harness_error(f"unusable oracle {d}/in.json: {e}"), tid)
        try:
            got = parse_json_stream(out.decode('utf-8', 'replace'))
        except json.JSONDecodeError:
            return ('diff', tid)   # the processor emitted malformed JSON
        return ('pass' if got == exp else 'diff', tid)

def score(cmd, dirs, axis, timeout, workers):
    reason = tester_available(cmd)
    if reason:
        harness_error(reason)
    cats = {}
    fails = []
    def work(d):
        if reason:   # tester cannot start: skip what score_one would skip, fail the rest
            return ('skip' if no_oracle(d, axis) else 'harness-error', test_id(d))
        return score_one(cmd, d, axis, timeout)
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for cat, tid in ex.map(work, dirs):
            cats[cat] = cats.get(cat, 0) + 1
            if cat in ('diff', 'reject', 'err-miss', 'timeout', 'harness-error'):
                fails.append((cat, tid))
    return cats, fails

# processor -> (event tester name or None, json tester name or None)
DOCKER = {
    'c-libfyaml':        ('c-libfyaml-event',        'c-libfyaml-json'),
    'c-libyaml':         ('c-libyaml-event',          None),
    'cpp-yamlcpp':       ('cpp-yamlcpp-event',        None),
    'dotnet-yamldotnet': ('dotnet-yamldotnet-event', 'dotnet-yamldotnet-json'),
    'hs-hsyaml':         ('hs-hsyaml-event',         'hs-hsyaml-json'),
    'java-snakeyaml':    ('java-snakeyaml-event',    'java-snakeyaml-json'),
    'js-jsyaml':         (None,                      'js-jsyaml-json'),
    'js-yaml':           ('js-yaml-event',           'js-yaml-json'),
    'lua-lyaml':         (None,                      'lua-lyaml-json'),
    'nim-nimyaml':       ('nim-nimyaml-event',        None),
    'perl-pp':           ('perl-pp-event',           'perl-pp-json'),
    'perl-pplibyaml':    ('perl-pplibyaml-event',    'perl-pplibyaml-json'),
    'perl-refparser':    ('perl-refparser-event',     None),
    'perl-syck':         (None,                      'perl-syck-json'),
    'perl-tiny':         (None,                      'perl-tiny-json'),
    'perl-xs':           (None,                      'perl-xs-json'),
    'perl-yaml':         (None,                      'perl-yaml-json'),
    'py-pyyaml':         ('py-pyyaml-event',         'py-pyyaml-json'),
    'py-ruamel':         ('py-ruamel-event',         'py-ruamel-json'),
    'ruby-psych':        (None,                      'ruby-psych-json'),
    'raku-yamlish':      (None,                      'raku-yamlish-json'),
}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', required=True)
    ap.add_argument('--container', default='yamlall')
    ap.add_argument('--axis', choices=['event', 'json', 'both'], default='both')
    ap.add_argument('--timeout', type=float, default=5.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--l4yaml-event', default=None)
    ap.add_argument('--l4yaml-json', default=None)
    ap.add_argument('--only', default=None, help='comma-separated processor ids')
    ap.add_argument('--out', default=None)
    args = ap.parse_args()

    dirs = leaf_dirs(args.data)
    print(f"# {len(dirs)} leaf tests in data form", file=sys.stderr)

    # Build processor -> {axis: cmd}
    procs = {}
    for pid, (ev, js) in DOCKER.items():
        procs[pid] = {}
        if ev: procs[pid]['event'] = ['docker', 'exec', '-i', args.container, ev]
        if js: procs[pid]['json']  = ['docker', 'exec', '-i', args.container, js]
    procs['L4YAML'] = {}
    if args.l4yaml_event: procs['L4YAML']['event'] = [args.l4yaml_event]
    if args.l4yaml_json:  procs['L4YAML']['json']  = [args.l4yaml_json]

    only = set(args.only.split(',')) if args.only else None
    axes = ['event', 'json'] if args.axis == 'both' else [args.axis]

    results = {}
    harness_errors = 0
    for pid in sorted(procs):
        if only and pid not in only:
            continue
        results[pid] = {}
        for axis in axes:
            if axis not in procs[pid]:
                continue
            cats, fails = score(procs[pid][axis], dirs, axis, args.timeout, args.workers)
            results[pid][axis] = {'cats': cats, 'fails': fails}
            harness_errors += cats.get('harness-error', 0)
            correct = cats.get('pass', 0) + cats.get('err-ok', 0)
            total = sum(v for k, v in cats.items() if k != 'skip')
            print(f"{pid:20s} {axis:5s}  correct={correct:3d}/{total:3d}  "
                  f"{dict(sorted(cats.items()))}", file=sys.stderr)

    if args.out:
        json.dump(results, open(args.out, 'w'), indent=1)
        print(f"# wrote {args.out}", file=sys.stderr)
    if harness_errors:
        print(f"# {harness_errors} harness-error result(s): the harness, not a "
              f"processor, failed — these scores are not publishable", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()
