import os
from os import listdir
from os.path import isdir, join, exists
import shutil
import glob
import subprocess
import re
import json
import contextlib
from .REMatcher import REMatcher


class RunTest(object):
    '''
        Represents a test runner that runs a list of tests and reports the regression test results.

        Args:
            test (str): The name of the test.
            test_list (str): The name of the test list.
            tag (str): The tag for the regression test.
            seed (str): The seed value for the tests.
            params (dict): The custom parameters for the tests.

        Attributes:
            original_directory (str): The original working directory.
            repo_root (str): The root directory of the repository.
            env: The environment variables for the tests.
            config_dct (dict): The configuration dictionary.
            test_list (str): The name of the test list.
            tag (str): The tag for the regression test.
            test (str): The name of the test.
            seed (str): The seed value for the tests.
            params (dict): The custom parameters for the tests.
            regression_dir (str): The directory for the regression test results.

        Example:
            ```python
            instance = RunTest(test="my_test", test_list="test_list", tag="runtest", seed="12345", params={"param1": "value1", "param2": "value2"})
            instance.run_test_list()
            ```
    '''

    def __init__(self, test=None, test_list=None, tag='runtest', seed=None, params=None):
        # Save the current directory
        self.original_directory = os.getcwd()
        # get the repo root
        print('Finding REPO_ROOT')
        self.repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
        self.env = os.environ.copy()
        self.env['REPO_ROOT'] = self.repo_root
        print(f'    REPO_ROOT={self.repo_root}')
        config_file = f'{self.repo_root}/bin/config.json'
        with open(config_file, 'r') as f:
            self.config_dct = json.load(f)
        self.test_list = test_list
        self.tag = tag
        self.test = test
        self.seed = seed
        self.params = params
        self.regression_dir = f'{self.repo_root}/regression/{tag}'
        self.regression_dir = RunTest.get_unique_dir_name(self.regression_dir)


    def _ready_run_area(self):
        os.mkdir(self.regression_dir)
        cleanall = f'{self.repo_root}/{self.config_dct["make_clean"]}'
        shutil.copy(cleanall, self.regression_dir)


    def run_test_list(self):
        '''
        Runs a list of tests and reports the regression test results.

        Args:
            self

        Returns:
            None

        Example:
            ```python
            instance = TestRunner()
            instance.run_test_list()
            ```
        '''
        self._ready_run_area()
        try:
            json_file_path = f"{self.repo_root}/{self.config_dct['test_lists'][self.test_list]}"
        except KeyError:
            print(f'Unknown test list {self.test_list}')
            exit(-1)

        # Read JSON file
        print(f'Loading Test List: {json_file_path}')
        with open(json_file_path, 'r') as f:
            test_list_json = json.load(f)

        fail_count = 0
        fail_list = []
        print('Running tests')
        for test_count, test_entry in enumerate(test_list_json):
            test_path = test_entry['test']
            test = test_path.split('/')[-1]
            if len(test) == 0:
                test = test_path.split('/')[-2]
            print(f'    {test}')

            seed = test_entry.get('seed', 1234)   # Default to None if 'seed' is not in dict
            params = test_entry.get('param', {})  # Default to empty dict if 'param' is not in dict

            pass_or_fail = self.run_make(self.repo_root, test, test_path, self.regression_dir, self.env, seed, params)
            if pass_or_fail is False:
                fail_count += 1
                fail_list.append(test)

        self.report_regression(test_count+1, fail_count, fail_list)
        # Change back to the original directory
        os.chdir(self.original_directory)


    def report_regression(self, test_count, fail_count, fail_list):
        '''
        Reports the regression test results.

        Args:
            test_count (int): The total number of tests.
            fail_count (int): The number of failed tests.
            fail_list (list): A list of failed test items.

        Returns:
            None

        Example:
            ```python
            test_count = 10
            fail_count = 2
            fail_list = ["Test 1", "Test 2"]

            report_regression(test_count, fail_count, fail_list)
            ```
        '''
        report_str = f'''
        ======================================================================
        Test Count = {test_count+1}        Failures = {fail_count}
        ======================================================================
        Failure List:
        '''
        for item in fail_list:
            report_str += f'    {item}\n'
        print(report_str)
        with open(f'{self.regression_dir}/report.txt', 'w') as file:
            file.write(report_str)


    @staticmethod
    def get_unique_dir_name(base_name):
        '''
        Generates a unique directory name based on the given base name.

            Args:
                base_name (str): The base name for the directory.

            Returns:
                str: The unique directory name.

            Example:
                ```python
                base_name = "directory"
                unique_dir_name = get_unique_dir_name(base_name)
                print(unique_dir_name)  # Output: directory.0
                ```
        '''
        counter = 0
        new_name = base_name
        while os.path.exists(new_name):
            new_name = f'{base_name}.{counter}'
            counter += 1
        return new_name


    @staticmethod
    def process_results(output_file):  # sourcery skip: extract-method
        '''
        Processes the results from an output file.

        Args:
            output_file (str): The path to the output file.

        Returns:
            bool: True if there are no test failures, False otherwise.

        Example:
            ```python
            output_file = "results.txt"
            test_passed = process_results(output_file)
            if test_passed:
                print("All tests passed!")
            else:
                print("Some tests failed.")
            ```
        '''
        with open(output_file, 'r') as f:
            line_list = [line.strip() for line in f.readlines()]

        for line in line_list:
            m = REMatcher(line)
            if m.match(r'.*TESTS=(\d+) PASS=(\d+) FAIL=(\d+) SKIP=(\d+).*'):
                tests_tot = int(m.group(1))
                tests_pass = int(m.group(2))
                tests_fail = int(m.group(3))
                tests_skip = int(m.group(4))
                # print(f'found the results line... {tests_tot=} {tests_pass=} {tests_fail=} {tests_skip=}')
                return tests_fail <= 0
        return False


    @staticmethod
    def update_makefile(makefile_path: str, seed: str, params: dict):
        '''
        Updates the makefile with the provided seed and parameters.

        Args:
            makefile_path (str): The path to the makefile.
            seed (str): The seed value to update in the makefile.
            params (dict): The custom parameters to update in the makefile.

        Returns:
            None

        Example:
            ```python
            makefile_path = "Makefile"
            seed = "12345"
            params = {"param1": "value1", "param2": "value2"}

            update_makefile(makefile_path, seed, params)
            ```
        '''
        new_lines = []
        with open(makefile_path, 'r') as f:
            lines = f.readlines()
            for line in lines:
                if "COMPILE_ARGS" in line and "export SEED" not in line and not params:
                    continue
                
                if "export SEED" in line and seed is not None:
                    line = f"export SEED={seed}\n"

                new_lines.append(line)
            
        if params:
            param_str = " ".join([f"-P $(DUT).{k}={v}" for k, v in params.items()])
            new_lines.append(f"COMPILE_ARGS += {param_str}\n")
        
        with open(makefile_path, 'w') as f:
            f.writelines(new_lines)


    @staticmethod
    def run_make(repo_root: str, test: str, base_test_path: str, path_out: str, env, seed: str, params: dict):
        '''
        Runs a make command for a specific test with custom parameters.

        Args:
            repo_root (str): The root directory of the repository.
            test (str): The name of the test.
            base_test_path (str): The base path of the test.
            path_out (str): The output path for the test results.
            env: The environment variables for the make command.
            seed (str): The seed value for the test.
            params (dict): The custom parameters for the test.

        Returns:
            bool: True if the test passes, False otherwise.

        Example:
            ```python
            repo_root = "/path/to/repo"
            test = "my_test"
            base_test_path = "tests"
            path_out = "/path/to/output"
            env = {"VAR": "value"}
            seed = "12345"
            params = {"param1": "value1", "param2": "value2"}

            test_passed = run_make(repo_root, test, base_test_path, path_out, env, seed, params)
            if test_passed:
                print("Test passed!")
            else:
                print("Test failed.")
            ```
        '''
        # Build a custom folder name based on the seed and parameters
        folder_suffix = f"seed_{seed}"
        for param, value in params.items():
            folder_suffix += f"_{param}_{value}"
        
        # Combine the test name and custom folder suffix
        custom_test_folder = f"{test}_{folder_suffix}"
        
        # Update the test path
        regression_test_path = os.path.join(path_out, custom_test_folder)

        # set up some local variables
        my_command = 'make'
        rpt = 'results.txt'
        output_file = f'{regression_test_path}/{rpt}'

        test_path = f'{repo_root}/{base_test_path}'
        if os.path.exists(test_path):
            shutil.copytree(test_path, regression_test_path)
            
        pycache = f'{regression_test_path}/__pycache__/'
        if os.path.exists(pycache):
            shutil.rmtree(pycache)

        os.chdir(f'{regression_test_path}')
        
        # Update Makefile based on the provided seed and params
        makefile_path = f'{regression_test_path}/Makefile'
        RunTest.update_makefile(makefile_path, seed, params)

        # Execute the command and capture both stdout and stderr
        try:
            completed_process = subprocess.run('make clean', shell=True, check=True, capture_output=True, text=True)
            completed_process = subprocess.run(my_command, env=env, shell=True, check=True, capture_output=True, text=True)
            output_text = completed_process.stdout

            # Save the output to a file
            with open(output_file, 'w') as file:
                file.write(output_text)

            # print("Command executed successfully. Output saved to:", output_file)
            pass_or_fail = RunTest.process_results(output_file)

        except subprocess.CalledProcessError as e:
            print(f'Error with {test=}')
            print("Command failed with exit code:", e.returncode)
            print("Error message:", e.stderr)
            # Save the output to a file
            with open(output_file, 'w') as file:
                file.write(e.stderr)
            pass_or_fail = False
        return pass_or_fail
