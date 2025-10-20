"""
Pytest configuration for perf_profiler tests

Provides:
- Logging configuration
- Test markers
- Build directory management
"""

import pytest
import os
import logging

def pytest_configure(config):
    """Configure pytest with custom settings"""

    # Create logs directory
    log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
    os.makedirs(log_dir, exist_ok=True)

    # Configure logging
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler(os.path.join(log_dir, 'test_perf_profiler.log')),
            logging.StreamHandler()
        ]
    )

    # Register custom markers
    config.addinivalue_line(
        "markers", "timestamp_mode: Tests using timestamp profiling mode"
    )
    config.addinivalue_line(
        "markers", "elapsed_mode: Tests using elapsed time profiling mode"
    )
    config.addinivalue_line(
        "markers", "single_channel: Single channel tests"
    )
    config.addinivalue_line(
        "markers", "multi_channel: Multiple channel tests"
    )
    config.addinivalue_line(
        "markers", "bug_demo: Tests that demonstrate known bugs"
    )
    config.addinivalue_line(
        "markers", "interface: Interface-level tests"
    )


@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    """Log test session completion"""
    logging.info("Performance profiler test session finished. Preserving all logs.")


def pytest_ignore_collect(collection_path, config):
    """Ignore logs directory during test collection"""
    return 'logs' in str(collection_path)
