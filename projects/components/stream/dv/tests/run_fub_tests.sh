#!/bin/bash
# Run all STREAM FUB tests in parallel using pytest-xdist
#
# Usage: ./run_fub_tests.sh
#
# This script runs all FUB-level tests for the STREAM subsystem using
# pytest's parallel execution feature (-n logical uses all available CPUs)

cd fub_tests && pytest -n logical -v --tb=short && cd ..
