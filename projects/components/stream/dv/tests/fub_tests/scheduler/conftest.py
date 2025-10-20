# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: conftest
# Purpose: pytest configuration for STREAM scheduler tests
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19

"""
pytest configuration for STREAM scheduler FUB tests.
"""

import os
import sys
import pytest


def pytest_configure(config):
    """Configure pytest for STREAM scheduler tests"""
    # Add stream dv directory to Python path
    stream_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
    if stream_dv_path in sys.path:
        sys.path.remove(stream_dv_path)
    sys.path.insert(0, stream_dv_path)
    
    # Create log directory
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)
    
    # Set log file path
    config.option.log_file = os.path.join(log_dir, "pytest_stream_scheduler.log")
