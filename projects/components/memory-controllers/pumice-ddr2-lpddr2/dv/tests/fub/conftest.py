"""
DDR2/LPDDR2 fub-level test conftest.

Wires up the import paths so test modules can:
  * `from TBClasses.shared.utilities import get_paths` — needs $REPO_ROOT/bin
    on sys.path (TBClasses is vendored under bin/ in the main repo, and
    under tests/sim/ in the DV repo)
  * `from tbclasses.pumice_rd_cmd_cam_tb import PumiceRdCmdCamTB` — needs the
    component dv/ directory on sys.path
"""

import os
import sys
import subprocess


def _ensure_path(p):
    p = os.path.abspath(p)
    if p in sys.path:
        sys.path.remove(p)
    sys.path.insert(0, p)


def pytest_configure(config):
    # Component dv/ → makes `tbclasses.*` importable
    dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
    _ensure_path(dv_path)

    # Repo bin/ → makes `TBClasses.*` importable (vendored snapshot)
    try:
        repo_root = subprocess.check_output(
            ['git', 'rev-parse', '--show-toplevel'],
            cwd=os.path.dirname(__file__),
        ).decode().strip()
        _ensure_path(os.path.join(repo_root, 'bin'))
    except Exception:
        pass

    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)


def pytest_ignore_collect(collection_path, config):
    path_str = str(collection_path)
    return 'logs' in path_str or 'local_sim_build' in path_str

# ----------------------------------------------------------------------
# NO REG_LEVEL -> TEST_LEVEL STAMP HERE. DELIBERATELY.
# ----------------------------------------------------------------------
# There used to be one, and while no wrapper exported a level it was the only
# thing mapping `make run-all-full-parallel` onto a depth: without it the grids
# fell back to FUNC and a FULL run quietly ran the FUNC matrix (measured on
# fub: 91 tests -> 79) while still reporting "passed".
#
# The trap is what it does once wrappers DO pass a level. cocotb_test's set_env
# applies extra_env first and then copies every os.environ entry over it, so a
# process-level TEST_LEVEL beats whatever a wrapper exported -- TOOL-016, see
# TBClasses.shared.test_levels.
#
# So this area now reads REG_LEVEL in each wrapper (the grids and the Group C
# depth tables) and exports TEST_LEVEL per cell. Removing this stamp without that
# wrapper change would have dropped the area to the FUNC default, which is why
# a comment stands here rather than a blank space. The tests that never read the
# level at all -- the directed single-scenario ones -- are unaffected either way.
