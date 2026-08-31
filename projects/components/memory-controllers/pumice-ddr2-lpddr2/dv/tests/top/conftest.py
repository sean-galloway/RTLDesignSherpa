"""pumice top-level test conftest.

Exists for the REG_LEVEL -> TEST_LEVEL bridge below. Without it this tier runs
whatever level TEST_LEVEL happens to hold rather than the one the make target
asked for.
"""

import os

# ----------------------------------------------------------------------
# REG_LEVEL -> TEST_LEVEL bridge
# ----------------------------------------------------------------------
# make/tests.mk drives the regression level through REG_LEVEL; this area's test
# modules read TEST_LEVEL, and they read it at MODULE IMPORT time
# (`_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC")` at file scope). conftest
# is imported before any test module, so setting it here is early enough.
#
# Without this bridge the Makefile convergence silently REDUCES coverage: the
# 4-line area Makefile sets REG_LEVEL=full, nothing reads it, TEST_LEVEL falls
# back to its FUNC default, and `make run-all-full-parallel` quietly runs the
# FUNC matrix. Measured: 91 fub tests -> 79. It still says "passed", which is
# exactly why it needs to be written down rather than remembered.
#
# REG_LEVEL wins over TEST_LEVEL, matching stream's conftest: the make target
# you typed is more explicit than an inherited environment variable.
_reg_level = os.environ.get('REG_LEVEL')
if _reg_level:
    os.environ['TEST_LEVEL'] = _reg_level.upper()
