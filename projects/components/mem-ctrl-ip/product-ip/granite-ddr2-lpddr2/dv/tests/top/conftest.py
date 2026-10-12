"""granite top-level test conftest.

Same REG_LEVEL -> TEST_LEVEL story as the pumice top conftest: no stamp here.
The parametrized tests export TEST_LEVEL per cell via level_env(), and
cocotb_test's set_env would let a stamped TEST_LEVEL beat it anyway
(tooling BUG-004, see TBClasses.shared.test_levels).
"""

import os

# ----------------------------------------------------------------------
# NO REG_LEVEL -> TEST_LEVEL STAMP HERE. DELIBERATELY.
# ----------------------------------------------------------------------
