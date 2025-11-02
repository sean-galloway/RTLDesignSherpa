"""
Testing configuration for pytest - CDC Counter Display Project

Configures logging, artifact preservation, and test collection settings
for the Nexys A7 CDC counter display simulation.
"""

import os
import logging
import pytest


def pytest_configure(config):
    """Configure pytest logging and directories"""
    # Create logs directory if it doesn't exist
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Configure log file for pytest itself
    config.option.log_file = os.path.join(log_dir, "pytest_run.log")
    config.option.log_file_level = "DEBUG"

    # Enable console logging
    config.option.log_cli = True
    config.option.log_cli_level = "INFO"


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """
    Called after whole test run finished, right before returning the exit status.
    Preserves all logs and build artifacts.
    """
    logging.info("Test session finished. Preserving all logs and build artifacts.")


def pytest_ignore_collect(collection_path, config):
    """
    Disable automatic test collection in certain directories.
    Prevents pytest from trying to collect tests from logs and build directories.
    """
    path_str = str(collection_path)

    # Ignore logs directory
    if 'logs' in path_str:
        return True

    # Ignore simulation build directory
    if 'sim_build' in path_str:
        return True

    # Ignore Verilator build artifacts
    if 'obj_dir' in path_str:
        return True

    return False


# Add project-specific pytest markers
def pytest_configure(config):
    """Register custom markers for test organization"""
    config.addinivalue_line(
        "markers", "cdc: tests specifically for CDC functionality"
    )
    config.addinivalue_line(
        "markers", "heartbeat: tests for heartbeat LED functionality"
    )
    config.addinivalue_line(
        "markers", "debounce: tests for button debouncing"
    )
    config.addinivalue_line(
        "markers", "display: tests for 7-segment display"
    )
