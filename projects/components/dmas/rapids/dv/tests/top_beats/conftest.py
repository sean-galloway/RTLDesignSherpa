"""rapids-top_beats test conftest.

Exists for the REG_LEVEL -> TEST_LEVEL bridge below. Without it this area runs
whatever level TEST_LEVEL happens to hold rather than the one the make target
asked for.
"""

import os

# ----------------------------------------------------------------------
# REG_LEVEL -> TEST_LEVEL bridge
# ----------------------------------------------------------------------
# make/tests.mk drives the regression level through REG_LEVEL; this area's test
# modules read TEST_LEVEL, and most read it at MODULE IMPORT time. conftest is
# imported before any test module, so setting it here is early enough.
#
# WITHOUT THIS BRIDGE THE MAKEFILE CONVERGENCE SILENTLY REDUCES COVERAGE: the
# 4-line area Makefile sets REG_LEVEL=full, nothing reads it, TEST_LEVEL falls
# back to its default, and `make run-all-full-parallel` quietly runs a smaller
# matrix while still reporting "passed". Measured on pumice fub during this
# conversion: 91 tests -> 79.
#
# REG_LEVEL wins over TEST_LEVEL, matching stream's conftest: the make target
# you typed is more explicit than an inherited environment variable.
_reg_level = os.environ.get('REG_LEVEL')
if _reg_level:
    os.environ['TEST_LEVEL'] = _reg_level.upper()
