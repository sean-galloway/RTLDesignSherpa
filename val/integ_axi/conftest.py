# conftest.py
import pytest

def pytest_addoption(parser):
    parser.addoption("--regression", action="store_true", help="Direct outputs to the regression area")
