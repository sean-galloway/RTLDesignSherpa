"""cache_sim golden harness for the amber parity grid (Task 10, PRD criterion 1).

One-shot node runner around bin/apps/cache_sim/js/model.js (node >= 18):
the shipped model bytes are loaded as TEXT, optionally patched with the
recorded LFSR extension (cache_sim_lfsr_extension.js), compiled into a fresh
Module COPY, and driven with the app's own parseAddressText/simulate entry
points.  The app itself is never edited.

DECISION D-9 recap:
  * cache_sim is word-addressed: a trace word address w maps to byte address
    w << 2, and blockSize = LINE_BYTES / 4 words (so block = w >> ilog2(LINE_BYTES/4)
    is exactly the amber line number).
  * read-only footprint: the model has no access-type field, so the parity TB
    replays every access as a read (a write would replay as the same-footprint
    write-allocate access anyway).
  * LRU / FIFO get exact NATIVE parity (unpatched model bytes).
  * RANDOM cannot parity natively (mulberry32 vs the RTL LFSR), so RANDOM
    cells run the recorded extension, which replays the amber_repl LFSR
    polynomial/seed (taps 32,22,2,1; REPL_SEED default 32'h0000_ACE1;
    sampled+advanced on every miss; no empty-way preference).

Runner validation lives in dv/tests/test_amber_parity.py
(test_amber_parity_golden_runner): it runs the app's own
bin/apps/cache_sim/test/run_tests.js expectations through THIS harness and
pins the extension's LFSR semantics against the Python reference below.

Author: RTL Design Sherpa
Created: 2026-10-09
"""

import json
import os
import re
import subprocess
import tempfile


REPL_SEED = 0x0000ACE1   # amber_repl REPL_SEED parameter default

MODEL_REL = os.path.join('bin', 'apps', 'cache_sim', 'js', 'model.js')
APP_SELFTEST_REL = os.path.join('bin', 'apps', 'cache_sim', 'test',
                                'run_tests.js')
EXTENSION_REL = os.path.join(
    'projects', 'components', 'cache-ip', 'amber-mesi-l1', 'dv', 'golden',
    'cache_sim_lfsr_extension.js')

# amber_repl_t encodings (amber_pkg) -> cache_sim policy names
POLICY_BY_REPL = {0: 'LRU', 1: 'TREE_PLRU', 2: 'FIFO', 3: 'RANDOM'}

# The node one-shot driver.  argv after the script:
#   model_path extension_path('-' = none) config_json trace_path mode
_NODE_DRIVER = r"""
'use strict';
const fs = require('fs');
const Module = require('module');

function fail(msg) {
    console.error('CACHE_SIM_HARNESS_ERROR: ' + msg);
    process.exit(2);
}

const args = process.argv.slice(1);
if (args.length !== 5) {
    fail('expected 5 args, got ' + args.length);
}
const modelPath = args[0];
const extPath = args[1];
const cfg = JSON.parse(args[2]);
const tracePath = args[3];
const mode = args[4];

let src = fs.readFileSync(modelPath, 'utf8');
if (extPath !== '-') {
    const ext = require(extPath);
    for (const p of ext.patches) {
        const hits = src.split(p.anchor).length - 1;
        if (hits !== 1) {
            fail('patch "' + p.label + '" anchor matched ' + hits +
                 ' times -- model.js drifted?');
        }
        src = src.replace(p.anchor, p.replacement);
    }
}

// Compile the (possibly patched) source into a COPY.  The shipped file is
// never touched; nothing is require()d from bin/apps/cache_sim/js directly.
const copy = new Module('cache_sim_parity_copy', null);
copy.filename = modelPath + '.parity_copy';
copy.paths = Module._nodeModulePaths(process.cwd());
copy._compile(src, copy.filename);
const CS = copy.exports;
if (!CS || typeof CS.simulate !== 'function') {
    fail('compiled copy did not export CACHESIM.simulate');
}

const text = fs.readFileSync(tracePath, 'utf8');
const addrs = CS.parseAddressText(text);
// simulate() runs the app's own validateAddresses internally
const res = CS.simulate({
    sets: cfg.sets,
    ways: cfg.ways,
    blockSize: cfg.block_size,
    policy: cfg.policy
}, addrs, cfg.seed >>> 0);
const out = { totals: res.totals, num_accesses: addrs.length };
if (mode === 'peraccess') {
    out.per_access = res.perAccess;
}
process.stdout.write(JSON.stringify(out));
"""


def repo_root() -> str:
    return os.environ.get('REPO_ROOT', subprocess.run(
        ['git', 'rev-parse', '--show-toplevel'], capture_output=True,
        text=True, check=True).stdout.strip())


class LfsrRng:
    """Python reference of the amber_repl RANDOM policy (the recorded
    extension must bit-match this): 32-bit Fibonacci LFSR, taps 32,22,2,1
    (zero-indexed bits 31,21,1,0), feedback shifted into the LSB.  next_int
    samples the truncated state as the victim way and THEN advances -- the
    RTL presents repl_victim_way combinationally on the sampling cycle and
    clocks the shift at the end of it."""

    def __init__(self, seed: int = REPL_SEED):
        self.state = seed & 0xFFFFFFFF

    def next_int(self, max_ways: int) -> int:
        way = self.state & (max_ways - 1)
        fb = ((self.state >> 31) ^ (self.state >> 21)
              ^ (self.state >> 1) ^ self.state) & 1
        self.state = ((self.state << 1) | fb) & 0xFFFFFFFF
        return way


def parse_address_text(text: str):
    """Faithful Python port of model.js parseAddressText (kept for TB-side
    cross-checks; the golden path itself uses the JS parser)."""
    out = []
    for line in text.splitlines():
        line = re.sub(r'//.*$', '', line).strip()
        if not line:
            continue
        if line[:2].lower() == '0x':
            out.append(int(line, 16) & 0xFFFFFFFF)
        else:
            out.append(int(line, 10) & 0xFFFFFFFF)
    return out


def format_address_text(addresses) -> str:
    return ''.join(f'{a & 0xFFFFFFFF}\n' for a in addresses)


def _node_cmd():
    node = 'node'
    return node


def run_golden(trace_path=None, addresses=None, *, sets: int, ways: int,
               line_bytes: int, policy: str, seed: int = 1,
               use_extension: bool = False, per_access: bool = False,
               root: str = None, timeout: int = 180) -> dict:
    """Run one cache_sim simulation and return {totals, num_accesses}.

    Exactly one of trace_path / addresses must be given.  policy is the
    cache_sim policy name ('LRU'/'FIFO'/'RANDOM'); with use_extension the
    recorded LFSR extension is applied to the compiled copy (RANDOM cells).
    """
    if (trace_path is None) == (addresses is None):
        raise ValueError('give exactly one of trace_path / addresses')
    root = root or repo_root()
    tmp = None
    try:
        if addresses is not None:
            tmp = tempfile.NamedTemporaryFile(
                'w', suffix='.txt', prefix='cache_sim_trace_', delete=False)
            tmp.write(format_address_text(addresses))
            tmp.close()
            trace_path = tmp.name
        cfg = {'sets': sets, 'ways': ways,
               'block_size': max(1, line_bytes // 4),
               'policy': policy, 'seed': seed & 0xFFFFFFFF}
        ext = os.path.join(root, EXTENSION_REL) if use_extension else '-'
        cmd = [_node_cmd(), '-e', _NODE_DRIVER,
               os.path.join(root, MODEL_REL), ext, json.dumps(cfg),
               trace_path, 'peraccess' if per_access else 'totals']
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout, cwd=root)
    finally:
        if tmp is not None:
            os.unlink(tmp.name)
    if proc.returncode != 0:
        raise RuntimeError(
            f'cache_sim golden run failed (rc={proc.returncode}): '
            f'{proc.stderr.strip() or proc.stdout.strip()}')
    line = proc.stdout.strip().splitlines()[-1]
    try:
        return json.loads(line)
    except json.JSONDecodeError as e:
        raise RuntimeError(f'golden runner returned non-JSON: '
                           f'{proc.stdout[:400]!r}') from e


def run_app_selftest(root: str = None, timeout: int = 120) -> str:
    """Run the app's own node test suite; returns its stdout.  Raises on
    any non-zero exit (the app is the golden reference -- it must be green
    before any amber comparison)."""
    root = root or repo_root()
    proc = subprocess.run([_node_cmd(), os.path.join(root, APP_SELFTEST_REL)],
                          capture_output=True, text=True, timeout=timeout,
                          cwd=root)
    if proc.returncode != 0:
        raise RuntimeError(
            f'cache_sim run_tests.js failed (rc={proc.returncode}):\n'
            f'{proc.stdout}\n{proc.stderr}')
    return proc.stdout


COUNT_KEYS = ('hits', 'misses', 'compulsory', 'capacity', 'conflict')


def check_totals(got: dict, exp: dict, label: str = '') -> list:
    """Exact-count comparator for the five PRD criterion-1 counters.
    Returns the list of human-readable differences (empty == exact parity).
    Never tolerance-based: any drift is a bug in RTL or harness."""
    diffs = []
    for k in COUNT_KEYS:
        if got.get(k) != exp.get(k):
            diffs.append(f'{label}{k}: amber={got.get(k)!r} '
                         f'cache_sim={exp.get(k)!r}')
    return diffs
