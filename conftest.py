"""Repo-root conftest: pin each test's SEED to its node id.

WHY THIS EXISTS
---------------
Every test wrapper in this repo picks its seed like this:

    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))

and `make/tests.mk` runs every area with `--reruns 3 --reruns-delay 1`.
`pytest-rerunfailures` re-executes the whole wrapper on a retry, so
`random.randint` was called AGAIN and the retry ran a DIFFERENT seed. A
failure that depended on the seed therefore got up to three fresh chances not
to happen, and the run printed `401 passed, 1 rerun`.

The evidence was destroyed twice over: `--tb=short` prints no traceback for a
rerun that eventually passes, and the per-test log is named for test and
worker, so the passing retry OVERWRITES the failing attempt's log. Observed
2026-09-07 on `test_math_fp8_e4m3_fma[params1]`, which passed outright in the
previous FULL run of the same suite and needed a retry in the next -- two
runs, two seeds, two outcomes, and no way to reproduce the failing one.

Randomised stimulus exists to find bugs the directed tests miss.
Retry-until-green is precisely the policy that discards those finds: the suite
does the search and then throws away the hits. See tooling BUG-008 (was TOOL-015) and
vault/handbook/dv/silent-fallbacks.md rule 13.

WHAT IT DOES
------------
The seed is derived from (session base, test node id), so:

  * a RERUN of the same test repeats the run it is retrying, and a
    seed-exposed failure fails all four attempts and gets REPORTED;
  * different tests still get different seeds;
  * a new session draws a new base, so randomised exploration across runs is
    unaffected;
  * `SEED=<n> pytest <test>` still wins -- an explicit seed is never
    overridden, which is what the "reproduce with" line in every TB log tells
    you to do.

The 338 test wrappers need no change: they already read the seed from the
environment, so this fills in the value they were defaulting.

Placed at the repo root because pytest resolves rootdir here even when
invoked from inside an area (`cd val/math && pytest`), so ONE file covers
every area and raw pytest as well as `make`. A per-area copy would be 20 files
that drift -- see silent-fallbacks rule 12.
"""

import hashlib
import inspect
import os
import random
import re

import pytest

# Read once, at import, before any test can set it. An explicitly supplied
# SEED is a reproduction request and must survive untouched.
_EXPLICIT_SEED = os.environ.get("SEED")

# Matches the range the wrappers themselves used.
_SEED_MAX = 100_000


# ONE base for the whole run, established in the controller process at import
# and exported so xdist workers inherit it.
#
# The first version of this asked xdist for PYTEST_XDIST_TESTRUNUID, which IS
# shared across workers -- but the controller does not have it yet when
# pytest_report_header runs, so the header printed a per-process random value
# that no worker used. Copying that base into RDS_SEED_BASE produced a THIRD
# seed space instead of replaying the run: a reproduction handle that silently
# did not reproduce, which is worse than not offering one.
#
# setdefault does both jobs: an explicit RDS_SEED_BASE from the caller is kept,
# and a generated one lands in os.environ, which execnet passes to every
# worker. So the base the header prints is provably the base every worker uses.
_SEED_BASE = os.environ.setdefault("RDS_SEED_BASE", str(random.randrange(2**32)))


def _session_base() -> str:
    return _SEED_BASE


def seed_for(nodeid: str) -> int:
    """Deterministic seed for a test id within this session.

    sha256 rather than hash(): PYTHONHASHSEED randomises str hashing per
    process, so hash() would hand the same test a different seed in each xdist
    worker and break the property this whole file exists to provide.
    """
    digest = hashlib.sha256(f"{_session_base()}:{nodeid}".encode()).hexdigest()
    return int(digest[:8], 16) % (_SEED_MAX + 1)


def _patch_cocotb_testcase_anchor():
    """Restore exact-name ``testcase=`` selection under cocotb 2.x.

    cocotb 1.x matched the ``TESTCASE`` env value against test NAMES
    exactly. cocotb 2.x reads ``COCOTB_TEST_FILTER`` and matches it with
    ``re.search`` over ``<module>.<test>`` fullnames. cocotb-test 0.3.0
    (latest; no fix released) passes its ``testcase=`` kwarg to
    ``COCOTB_TEST_FILTER`` UNANCHORED, so ``testcase='monitor_soak'``
    also selects ``monitor_soak_monlite`` -- every multi-test module runs
    ALL its tests in EVERY build (tooling BUG-015, observed on
    val/amba/test_axi_monitor_soak.py where the monlite test then fails
    against the pktgen DUT).

    The patch anchors each testcase as ``\\b<name>$`` before cocotb-test
    hands it to the simulator, restoring 1.x exact-name semantics for all
    ~80 call sites at once. No-op when cocotb-test is not importable, and
    idempotent. DELETE THIS when cocotb-test releases a fix that anchors
    the filter itself -- a double anchor is harmless regex, but the patch
    should not outlive its reason.
    """
    global _TESTCASE_ANCHOR_ACTIVE
    try:
        import cocotb_test.simulator as cts
    except Exception:
        return

    orig = cts.Simulator.__init__
    try:
        tc_pos = list(inspect.signature(orig).parameters).index("testcase") - 1
    except ValueError:
        tc_pos = None  # no testcase parameter: nothing to anchor

    def anchored(tc: str) -> str:
        # Plain identifiers at every call site; escape keeps the anchor
        # honest if a future site passes regex metacharacters.
        return r"\b" + re.escape(tc) + "$"

    def patched(self, *args, **kwargs):
        tc = kwargs.get("testcase")
        if tc is None and tc_pos is not None and len(args) > tc_pos:
            tc = args[tc_pos]
        if isinstance(tc, str):
            if "testcase" in kwargs:
                kwargs["testcase"] = anchored(tc)
            elif tc_pos is not None and len(args) > tc_pos:
                args = args[:tc_pos] + (anchored(tc),) + args[tc_pos + 1:]
        return orig(self, *args, **kwargs)

    cts.Simulator.__init__ = patched
    _TESTCASE_ANCHOR_ACTIVE = True


_TESTCASE_ANCHOR_ACTIVE = False
_patch_cocotb_testcase_anchor()


@pytest.fixture(autouse=True)
def rds_pin_seed(request):
    """Export SEED for this test, stable across its own reruns."""
    if _EXPLICIT_SEED is not None:
        yield
        return

    previous = os.environ.get("SEED")
    os.environ["SEED"] = str(seed_for(request.node.nodeid))
    try:
        yield
    finally:
        # Leave the environment as found, so a test that inspects SEED outside
        # its own execution does not see a neighbour's value.
        if previous is None:
            os.environ.pop("SEED", None)
        else:
            os.environ["SEED"] = previous


def pytest_report_header(config):
    """Show the seed base, so a whole run can be replayed.

    A seed you cannot see is a seed you cannot reproduce -- which was half of
    what made the rerun behaviour above so expensive to notice.
    """
    lines = []
    if _TESTCASE_ANCHOR_ACTIVE:
        lines.append("rds: cocotb-test testcase= anchored to exact-name "
                     "selection (BUG-015; remove when cocotb-test fixes it)")
    if _EXPLICIT_SEED is not None:
        lines.append(f"rds: SEED pinned to {_EXPLICIT_SEED} for every test (explicit)")
    else:
        lines.append(f"rds: seed base {_session_base()} "
                     f"(replay this run with RDS_SEED_BASE=<base>; "
                     f"one test with SEED=<n>)")
    return lines
