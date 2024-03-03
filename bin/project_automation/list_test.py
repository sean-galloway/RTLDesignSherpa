import os
import subprocess
import re
import json
import contextlib
import subprocess
from .REMatcher import REMatcher


class TestList(object):

    def __init__(self):
        # Save the current directory
        self.original_directory = os.getcwd()
        # get the repo root
        print('Finding REPO_ROOT')
        self.repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
        self.env = os.environ.copy()
        self.env['REPO_ROOT'] = self.repo_root


    def generate_run_test_commands(self, test_name_substring):
        """
        Generates a list of commands for running tests based on a given test name substring.

        Args:
            self: The instance of the class.

            test_name_substring (str): The substring to search for in the full test names.

        Returns:
            List[str]: A list of commands for running tests that match the given test name substring.

        Example:
            ```python
            test_name_substring = "arbiter"
            commands = generate_run_test_commands(test_name_substring)
            for cmd in commands:
                print(cmd)
            ```
        """
        # Load the configuration file
        repo_root = self.repo_root
        with open(os.path.join(repo_root, "bin/config.json"), 'r') as f:
            config = json.load(f)

        commands = []
        
        # Load the test list file
        for level in config['test_lists']:
            test_list_file = os.path.join(repo_root, config['test_lists'][level])
            with open(test_list_file, 'r') as f:
                test_list = json.load(f)
            
            # Generate commands for each list file
            for test_info in test_list:
                full_test_name = test_info['test']
                if test_name_substring in full_test_name:
                    seed = test_info.get('seed', 'None')
                    params = test_info.get('param', {})
                    params_str = ','.join(f"{k}={v}" for k, v in params.items())
                    
                    cmd = f"python run_test_wrap.py --test {full_test_name} --tag my_tag --seed {seed}"
                    if params_str:
                        cmd += f" --params {params_str}"
                    
                    commands.append(cmd)
        
        for cmd in commands:
            print(cmd)

        # # Example usage
        # test_name_substring = "arbiter"  # Replace this with the substring you are interested in
        # commands = generate_run_test_commands(test_name_substring)


    def create_json_file_from_dirs(self, path, json_file_name):
        """
            Creates a JSON file from a single directory with many 
                test directories.

            Args:
                path (str): The path to the directory containing the tests.
                json_file_name (str): The name of the JSON file to create.

            Returns:
                None

            Example:
                ```python
                path = "/path/to/tests"
                json_file_name = "test_list.json"

                create_json_file_from_dirs(path, json_file_name, repo_root)
                ```
        """

        test_list = []
        repo_root = self.repo_root
        print(f'{path=}')
        for dir_name in next(os.walk(path))[1]:
            print(f'{dir_name=}')
            test_path = os.path.join(path, dir_name)

            # Calculate the relative path after the repo root
            test_name = os.path.relpath(test_path, repo_root)
            test_dict = {"test": test_name}
            test = test_name.split('/')[-2]
            test_dict["test_name"] = test
            param_dict = {}

            # Read the Makefile
            with contextlib.suppress(FileNotFoundError):
                with open(os.path.join(test_path, "Makefile"), "r") as f:
                    lines = f.readlines()

                    # Parse for COMPILE_ARGS
                    for line in lines:
                        if re.match(r"^\s*#", line):
                            continue  # Skip comments

                        compile_args_match = re.findall(r'-P\s*\$\(DUT\)\.(\w+)=(\S+)', line)
                        for param, value in compile_args_match:
                            param_dict[param] = value

                    # Parse for SEED
                    for line in lines:
                        if re.match(r"^\s*#", line):
                            continue  # Skip comments

                        if seed_match := re.search(r'export SEED=(\w+)', line):
                            test_dict["seed"] = seed_match[1]

            test_dict["param"] = param_dict
            test_list.append(test_dict)

        # Sort the list of dictionaries by the 'test' key
        test_list.sort(key=lambda x: x['test'])

        # Create the JSON file
        with open(json_file_name, 'w') as f:
            json.dump(test_list, f, indent=4)