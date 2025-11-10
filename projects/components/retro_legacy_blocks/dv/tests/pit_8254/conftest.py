# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa

"""
Pytest configuration for PIT 8254 tests.
"""

import os
import pytest
import logging


def pytest_configure(config):
    """Configure pytest for PIT 8254 tests."""
    # Create logs directory
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Register markers
    config.addinivalue_line("markers", "basic: Basic functionality tests")
    config.addinivalue_line("markers", "medium: Extended feature tests")
    config.addinivalue_line("markers", "full: Stress and corner case tests")


def pytest_collection_modifyitems(config, items):
    """Modify test collection to add markers based on test names."""
    for item in items:
        # Add basic marker to basic tests
        if "basic" in item.nodeid.lower():
            item.add_marker(pytest.mark.basic)
        # Add medium marker to medium tests
        elif "medium" in item.nodeid.lower():
            item.add_marker(pytest.mark.medium)
        # Add full marker to full tests
        elif "full" in item.nodeid.lower():
            item.add_marker(pytest.mark.full)
