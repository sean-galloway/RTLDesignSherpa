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
