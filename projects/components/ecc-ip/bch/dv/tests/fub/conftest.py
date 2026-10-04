"""bch fub-level test conftest.

Wires the import paths so a test module can reach both halves of the DV
framework:

  * `from TBClasses.shared.tbbase import TBBase` -- needs $REPO_ROOT/bin
    on sys.path (TBClasses lives under bin/ in the main repo);
  * `from projects.components.ecc_ip.bch.dv.tbclasses.bch_model import BCHModel`
    -- needs the repo root on sys.path; the test modules add it themselves
    via `get_repo_root()`, and `projects/components/__init__.py`'s alias shim
    maps `ecc_ip`/`bch` onto the on-disk `ecc-ip/bch` directories.

Mirrors scoria's fub conftest, deliberately: the two areas' tests are read
side by side and a second shape to learn is a cost with no benefit.

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
    # Component dv/ -> makes `tbclasses.*` importable for tests that import
    # it directly instead of through the projects.components alias
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
