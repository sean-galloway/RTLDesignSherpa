"""Monitor-flow test config — puts the flow dv dir on sys.path (tbclasses import)."""
import os, sys, pytest

def pytest_configure(config):
    dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
    if dv_path not in sys.path:
        sys.path.insert(0, dv_path)
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)
