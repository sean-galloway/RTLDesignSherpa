#!/usr/bin/python3

import argparse
from project_automation.lint import Lint
import subprocess
import os
import subprocess

def main():
    parser = argparse.ArgumentParser(description="Lint and format Verilog files.")
    parser.add_argument("--format", action="store_true", help="Run the format function")
    parser.add_argument("--lint", action="store_true", help="Run the lint function")

    args = parser.parse_args()

    if not args.format and not args.lint:
        parser.error("Please specify at least one of --format or --lint")

    lint_instance = Lint()

    if args.format:
        lint_instance.run_verible_format()

    if args.lint:
        lint_instance.run_lint()

if __name__ == "__main__":
    main()
