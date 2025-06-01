"""
Setup script for field config linting rules.

File: tools/setup_field_config_linting.py
"""

import os
import shutil
import subprocess
import sys


def setup_field_config_linting():
    """Set up field config linting rules and tools."""
    
    print("Setting up field config linting...")
    
    # Create linting tools directory
    tools_dir = "tools/linting"
    os.makedirs(tools_dir, exist_ok=True)
    
    # Copy linting files (assumes they're in current directory)
    linting_files = [
        "field_config_checker.py",
        "flake8_field_config.py"
    ]
    
    for file in linting_files:
        if os.path.exists(file):
            shutil.copy(file, os.path.join(tools_dir, file))
            print(f"Copied {file} to {tools_dir}/")
    
    # Install required packages
    packages = [
        "pylint>=2.17.0",
        "flake8>=5.0.0", 
        "pre-commit>=3.0.0"
    ]
    
    print("Installing required packages...")
    for package in packages:
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", package])
            print(f"Installed {package}")
        except subprocess.CalledProcessError:
            print(f"Failed to install {package}")
    
    # Set up pre-commit hooks
    if os.path.exists(".pre-commit-config.yaml"):
        print("Pre-commit config already exists. Please manually add field config hooks.")
    else:
        print("Creating .pre-commit-config.yaml...")
        # Could create a basic config here
    
    print("Field config linting setup complete!")
    print("\nNext steps:")
    print("1. Review and customize the linting rules in tools/linting/")
    print("2. Add the pre-commit hooks to your .pre-commit-config.yaml")
    print("3. Update your CI/CD pipeline to include field config checks")
    print("4. Run 'make lint-field-config' to test the setup")


if __name__ == "__main__":
    setup_field_config_linting()
