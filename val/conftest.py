"""Validation-wide pytest defaults (val/<area>).

One job today: make the simulator default explicit when the caller's shell
skipped ``source env_python``.

env_python exports ``SIM=verilator``; every flow Makefile assumes it. A bare
``pytest val/...`` from an un-sourced shell leaves SIM unset, and cocotb-test's
library default is **icarus** — which on this host dies at time 0: the
oss-cad-suite vvp wrapper forces its own glibc-2.35 libm, and system
libpython3.12 requires glibc 2.38 (tooling BUG-016, 2026-10-08). The failure
presents as an empty-xUnit ParseError that smells like an RTL/DV break.

Rules here, deliberately narrow:

- ONLY default when SIM is unset. A deliberate ``export SIM=icarus`` is
  respected untouched — this guard exists to kill the *silent* default, not
  to block intentional icarus runs.
- No override, ever: env_python's value wins when present.

The warning prints to stderr at import so it lands in the pytest header,
not buried in a per-cell log.
"""

import os
import sys

if "SIM" not in os.environ:
    os.environ["SIM"] = "verilator"
    print(
        "[val/conftest] SIM not set — env_python was not sourced; "
        "defaulting SIM=verilator. (icarus legs cannot load libpython3.12 "
        "on this host — tooling BUG-016. Deliberate icarus: export SIM=icarus "
        "explicitly.)",
        file=sys.stderr,
    )
