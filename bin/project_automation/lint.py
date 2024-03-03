import os
import subprocess
from os import listdir
from os.path import isfile, join, exists
import json
import glob
import subprocess
import re
from .REMatcher import REMatcher


class Lint(object):
    """
    A class for performing linting and formatting operations on RTL code.

    Args:
        None

    Attributes:
        original_directory (str): The current directory.
        repo_root (str): The root directory of the Git repository.
        env (dict): The environment variables.
        config_dct (dict): The configuration dictionary.

    Methods:
        run_verible_format: Runs the Verible code formatter on the RTL code.
        run_lint: Runs linting operations on the RTL code.
        _run_verible_single: Runs the Verible linter on a single RTL file.
        _run_lint_single: Runs the Yosys linter on a single RTL file.
        _delete_files_in_directory: Deletes all files in a directory.
    """

    def __init__(self):
        # Save the current directory
        self.original_directory = os.getcwd()
        # get the repo root
        print('Finding REPO_ROOT')

        try:
            # Run the 'git rev-parse --show-toplevel' command to get the root directory
            result = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
            self.repo_root = result.strip()
            print(f"The root directory of the Git repository is: {self.repo_root}")
        except subprocess.CalledProcessError:
            print("Not a valid Git repository or an error occurred.")

        full_path = f'{self.repo_root}/reports/lint/'
        if not os.path.exists(full_path):
            # If it doesn't exist, create it
            os.makedirs(full_path)
        full_path = f'{self.repo_root}/reports/verible/'
        if not os.path.exists(full_path):
            # If it doesn't exist, create it
            os.makedirs(full_path)

        self.env = os.environ.copy()
        self.env['REPO_ROOT'] = self.repo_root
        print(f'    REPO_ROOT={self.repo_root}')
        config_file = f'{self.repo_root}/bin/config.json'
        with open(config_file, 'r') as f:
            self.config_dct = json.load(f)


    def run_verible_format(self):
        rpt_path = f'{self.repo_root}/reports/format_logs/'
        self._delete_files_in_directory(rpt_path)
        for rtl_dir in self.config_dct['rtl_dirs']:
            path_in = f'{self.repo_root}/{rtl_dir}'
            file_list = [f for f in listdir(path_in) if isfile(join(path_in, f))]
            for dut in sorted(file_list):
                if '.sv' not in dut:
                    continue
                rpt = dut.replace('.sv', '.txt')
                output_file = f'{rpt_path}{rpt}'
                my_command = f'verible-verilog-format --indentation_spaces 4 --inplace {path_in}/{dut}'

                try:
                    completed_process = subprocess.run(my_command, shell=True, check=True, capture_output=True, text=True)
                    output_text = completed_process.stdout

                    # Save the output to a file
                    with open(output_file, 'w') as file:
                        file.write(output_text)

                    # print("Command executed successfully. Output saved to:", output_file)

                except subprocess.CalledProcessError as e:
                    print("Command failed with exit code:", e.returncode)
                    print("Error message:", e.stderr)
                    # Save the output to a file
                    with open(output_file, 'w') as file:
                        file.write(e.stderr)


    def run_lint(self):
        lint_dir = self.config_dct['lint_reports']['lint']
        path_lint_rpt = join(self.repo_root, lint_dir)
        verible_dir = self.config_dct['lint_reports']['verible']
        path_verible_rpt = join(self.repo_root, verible_dir)
        
        self._delete_files_in_directory(path_lint_rpt)
        self._delete_files_in_directory(path_verible_rpt)

        for rtl_dir in self.config_dct['rtl_dirs']:
            path_in = f'{self.repo_root}/{rtl_dir}'
            file_list = [f for f in listdir(path_in) if isfile(join(path_in, f))]

            for dut in sorted(file_list):
                if '.sv' not in dut:
                    continue
                # print(f'Working on {dut}')
                rpt = dut.replace('.sv', '.txt')
                self._run_lint_single(dut, path_in, path_lint_rpt, rpt)           
                self._run_verible_single(dut, path_in, path_verible_rpt, rpt)           


    def _run_verible_single(self, dut: str, path_in: str, path_rpt: str, rpt: str):
        # sourcery skip: class-extract-method
        my_command = f'verible-verilog-lint {path_in}/{dut}'
        
        output_file = f'{path_rpt}{rpt}'

        # Execute the command and capture both stdout and stderr
        try:
            completed_process = subprocess.run(my_command, shell=True, check=True, capture_output=True, text=True)
            output_text = completed_process.stdout

            # Save the output to a file
            with open(output_file, 'w') as file:
                file.write(output_text)

            # print("Command executed successfully. Output saved to:", output_file)

        except subprocess.CalledProcessError as e:
            print("Command failed with exit code:", e.returncode)
            print("Error message:", e.stderr)
            # Save the output to a file
            with open(output_file, 'w') as file:
                file.write(e.stderr)


    def _run_lint_single(self, dut: str, path_in: str, path_rpt: str, rpt: str):
        my_command = f'yowasp-yosys -Q -p "read_verilog -sv {path_in}/{dut}; ; proc;"'
        rpt = dut.replace('.sv', '.txt')
        output_file = f'{path_rpt}/{rpt}'

        # Execute the command and capture both stdout and stderr
        try:
            completed_process = subprocess.run(my_command, shell=True, check=True, capture_output=True, text=True)
            output_text = completed_process.stdout

            # Save the output to a file
            with open(output_file, 'w') as file:
                file.write(output_text)

            # print("Command executed successfully. Output saved to:", output_file)

        except subprocess.CalledProcessError as e:
            print("Command failed with exit code:", e.returncode)
            print("Error message:", e.stderr)
            # Save the output to a file
            with open(output_file, 'w') as file:
                file.write(e.stderr)


    @staticmethod
    def _delete_files_in_directory(directory_path):
        # Check if the directory exists
        if not os.path.exists(directory_path):
            print(f"Directory '{directory_path}' does not exist.")
            return

        try:
            # List all files in the directory
            files = os.listdir(directory_path)

            # Iterate through the files and delete each one
            for file_name in files:
                file_path = os.path.join(directory_path, file_name)
                if os.path.isfile(file_path):
                    os.remove(file_path)
                    # print(f"Deleted: {file_path}")

            print(f"All files in '{directory_path}' have been deleted.")

        except Exception as e:
            print(f"An error occurred: {str(e)}")


