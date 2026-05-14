"""Shared pytest_configure / pytest_sessionfinish / pytest_ignore_collect
helpers, used by per-area conftest.py files across the repo.

Goal: each area's conftest collapses to a thin wrapper that just
declares its area-specific bits (log basename, markers, fixtures)
and delegates the boilerplate (log/coverage dir creation, log file
config, console logging, marker registration, coverage aggregation,
scratch-dir ignore) to one place.

The shared helpers deliberately do NOT touch xdist / numprocesses.
If a particular area needs to cap parallelism, it should do that
via the Makefile / command line (`-n <N>`), not by clobbering
`config.option.numprocesses` in a conftest -- which silently turns
`make run-parallel` into a sequential run regardless of the user's
intent.
"""

import logging
import os
from typing import Iterable, Tuple


def configure(config,
              caller_file: str,
              log_basename: str,
              markers: Iterable[str] = ()) -> None:
    """Common ``pytest_configure`` body.

    Args:
        config: the pytest Config object passed to ``pytest_configure``.
        caller_file: the conftest's ``__file__``; ``logs/`` and
            ``coverage_data/`` are created alongside it.
        log_basename: file name written under ``logs/`` (e.g.
            ``'pytest_bridge.log'``).
        markers: iterable of ``'<name>: <description>'`` strings to
            register with pytest. Area-specific.
    """
    base_dir = os.path.dirname(os.path.abspath(caller_file))
    log_dir = os.path.join(base_dir, 'logs')
    os.makedirs(log_dir, exist_ok=True)

    if os.environ.get('COVERAGE', '0') == '1':
        coverage_dir = os.path.join(base_dir, 'coverage_data')
        for sub in ('per_test', 'merged', 'reports'):
            os.makedirs(os.path.join(coverage_dir, sub), exist_ok=True)
        logging.info(f'Coverage enabled. Data will be stored in: {coverage_dir}')

    config.option.log_file = os.path.join(log_dir, log_basename)
    config.option.log_file_level = 'DEBUG'
    config.option.log_cli = True
    config.option.log_cli_level = 'INFO'

    for marker in markers:
        config.addinivalue_line('markers', marker)


def sessionfinish(caller_file: str, area_name: str) -> None:
    """Common ``pytest_sessionfinish`` body. Aggregates coverage when
    ``COVERAGE=1`` is set; otherwise just logs a session-end marker.

    Args:
        caller_file: conftest's ``__file__``.
        area_name: human-readable area name (e.g. ``'Bridge'``); shows
            up in the merged coverage report's title.
    """
    logging.info(
        f'{area_name} test session finished. Preserving all logs and build artifacts.'
    )
    if os.environ.get('COVERAGE', '0') == '1':
        from cov_utils.conftest_coverage import aggregate_all_coverage
        base_dir = os.path.dirname(os.path.abspath(caller_file))
        aggregate_all_coverage(base_dir, area_name)


# Directories that should NEVER be scanned for tests, regardless of area.
# Includes `local_sim_build` so per-test sim build trees don't get picked
# up as test modules (they may contain `dump.fst`/`coverage.dat`/etc.).
_DEFAULT_IGNORED = ('logs', 'coverage_data', 'local_sim_build', 'reports')


def ignore_collect(collection_path,
                   extra_ignored: Tuple[str, ...] = ()) -> bool:
    """Common ``pytest_ignore_collect`` body. Returns True for paths
    pytest should NOT descend into.

    Args:
        collection_path: the path pytest is considering.
        extra_ignored: area-specific directory names to skip in addition
            to the defaults (``logs``, ``coverage_data``,
            ``local_sim_build``, ``reports``).
    """
    path_str = str(collection_path)
    return (
        any(d in path_str for d in _DEFAULT_IGNORED)
        or any(d in path_str for d in extra_ignored)
    )
