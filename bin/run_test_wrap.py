#!/usr/bin/python3

import argparse
from project_automation.run_test import RunTest

def parse_params(param_str):
    param_dict = {}
    for param in param_str.split(','):
        key, value = param.split('=')
        param_dict[key] = value
    return param_dict

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='''RunTest Wrapper

    Single Test Example:
        python run_test.py --test my_test --tag my_tag --seed 1234 --params N=8,M=16

    Test List Example:
        python run_test.py --testlist my_test_list --tag my_tag
''')
    
    # Define command-line options
    parser.add_argument('--test', type=str, help='Name of the test to run')
    parser.add_argument('--testlist', type=str, help='Name of the test list to run from config')
    parser.add_argument('--tag', type=str, help='Tag string for the run', default='runtest')
    parser.add_argument('--seed', type=str, help='Seed value for the test', default=None)
    parser.add_argument('--params', type=str, help='Comma-separated test parameters in the format key1=value1,key2=value2,...', default=None)
    parser.add_argument('--randomize', action='store_true', dest='randomize', default=False, help='Enable randomization, usually only meaningful for running regressions')

    # Parse command-line arguments
    args = parser.parse_args()

    # Convert comma-separated parameter string to dictionary
    params = parse_params(args.params) if args.params else None

    # Instantiate RunTest class
    if args.test:
        run_test_obj = RunTest(test=args.test, tag=args.tag, seed=args.seed, params=params)
        run_test_obj.run_test()
    elif args.testlist:
        run_test_obj = RunTest(test_list=args.testlist, tag=args.tag, randomize=args.randomize)
        run_test_obj.run_test_list()
    else:
        print("Either --test or --testlist must be provided.")
