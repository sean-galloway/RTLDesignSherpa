#!/usr/bin/python3

import argparse
from project_automation.list_test import TestList  # Assuming your class is at val_project/test_list.py

def main():
    parser = argparse.ArgumentParser(description='Test List Wrapper')
    
    # Add argument for finding test commands by partial name
    parser.add_argument('--find', type=str, help='Partial test name to find test commands')
    
    # Add argument for generating JSON test list
    parser.add_argument('--list', type=str, help='Name of the JSON file to create for test list')
    parser.add_argument('--path', type=str, help='Path to the directory containing the tests')

    args = parser.parse_args()

    # Show help if no arguments are provided
    if not any(vars(args).values()):
        parser.print_help()
        return

    # Create a TestList object
    test_list_obj = TestList()

    if args.find:
        # Generate run_test.py commands for tests that contain the given substring
        test_list_obj.generate_run_test_commands(args.find)

    if args.list and args.path:
        # Create a JSON file from a directory with many test directories
        test_list_obj.create_json_file_from_dirs(args.path, args.list)

if __name__ == '__main__':
    main()
