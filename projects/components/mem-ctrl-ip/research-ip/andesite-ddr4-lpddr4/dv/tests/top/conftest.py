"""andesite (DDR4/LPDDR4) top-level test conftest.

Wires the import paths so a test module can reach both halves of the DV
framework:

  * `from TBClasses.shared.utilities import get_paths` -- needs $REPO_ROOT/bin
    on sys.path (TBClasses lives under bin/ in the main repo and under
    tests/sim/ in the DV repo);
  * `from tbclasses.andesite_cmd_arbiter_tb import AndesiteCmdArbiterTB` -- needs
    this component's dv/ directory on sys.path.

Mirrors pumice's, deliberately: the two areas' tests are read side by side and
a second shape to learn is a cost with no benefit.

`pytest_ignore_collect` keeps collection out of logs/ and local_sim_build/.
Nothing there is a test today, but those trees fill with generated files and a
collection error in one of them aborts the whole directory -- which reads as
"the suite is broken" rather than "pytest wandered into a build tree".
"""

import os
import subprocess
import sys


def _ensure_path(p):
    p = os.path.abspath(p)
    if p in sys.path:
        sys.path.remove(p)
    sys.path.insert(0, p)


def pytest_configure(config):
    # Component dv/ -> makes `tbclasses.*` importable
    dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
    _ensure_path(dv_path)

    # Repo bin/ -> makes `TBClasses.*` importable
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
