"""
DDR2/LPDDR2 macro-level test conftest. Mirrors stream's macro conftest:
ensures the component dv directory is at sys.path[0] so test modules
can import `projects.components....dv.tbclasses.*`.
"""

import os
import sys


def pytest_configure(config):
    dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
    if dv_path in sys.path:
        sys.path.remove(dv_path)
    sys.path.insert(0, dv_path)

    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

# ----------------------------------------------------------------------
# NO REG_LEVEL -> TEST_LEVEL STAMP HERE. DELIBERATELY.
# ----------------------------------------------------------------------
# Nothing in this area reads the level -- not the three tests, not their
# testbench classes -- so the stamp was never load-bearing here and removing it
# changes nothing a run does. It is removed anyway so the TOOL-016 trap cannot
# bite the first test here that does start exporting a level: cocotb_test copies
# os.environ over extra_env, so a stamped TEST_LEVEL would silently override it.
