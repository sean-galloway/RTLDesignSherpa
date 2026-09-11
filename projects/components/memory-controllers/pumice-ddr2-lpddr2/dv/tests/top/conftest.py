"""pumice top-level test conftest.

Exists for the REG_LEVEL -> TEST_LEVEL bridge below. Without it this tier runs
whatever level TEST_LEVEL happens to hold rather than the one the make target
asked for.
"""

import os

# ----------------------------------------------------------------------
# NO REG_LEVEL -> TEST_LEVEL STAMP HERE. DELIBERATELY.
# ----------------------------------------------------------------------
# cocotb_test's set_env applies extra_env first and then copies every
# os.environ entry over it, so a stamped TEST_LEVEL beats whatever a wrapper
# exports -- TOOL-016, see TBClasses.shared.test_levels. The three tests here
# that grade depth now read REG_LEVEL themselves and export TEST_LEVEL per
# cell, so the stamp is no longer needed and would only get in the way. The two
# that never read the level -- core and top_geared -- are unaffected.
