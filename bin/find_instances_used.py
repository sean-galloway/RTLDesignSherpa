#!/usr/bin/python3

import os
import subprocess
import argparse
import re
import pprint
pp = pprint.PrettyPrinter(indent=4)

def parse_makefile(makefile_path, verilog_files):
    with open(makefile_path, 'r') as file:
        contents = file.read()

    pattern = r"VERILOG_SOURCES\s*=\s*((?:.*\\\n?)+)"
    match = re.search(pattern, contents, re.MULTILINE)

    used_paths = {}
    if match:
        sources_block = match[1]
        for line in sources_block.splitlines():
            line = line.strip().replace('\\', '').replace('$(REPO_ROOT)/rtl/common/', '').strip()
            for vf in verilog_files:
                vf_basename = os.path.basename(vf)
                if vf_basename in line:
                    if vf_basename not in used_paths:
                        used_paths[vf_basename] = []
                    used_paths[vf_basename].append(makefile_path.replace('Makefile', '').replace('$(REPO_ROOT)/val/common_level0/', ''))
    return used_paths

def list_sv_files(path):
    sv_files = []
    for root, dirs, files in os.walk(path):
        sv_files.extend(os.path.join(root, file) for file in files if file.endswith('.sv'))
    return sv_files

def main(args):
    verilog_files = list_sv_files(args.verilog_path) if args.verilog_path else []
    results = {}

    for file in verilog_files:
        file_key = os.path.basename(file)
        results[file_key] = []

    for subdir, dirs, files in os.walk(args.path):
        for file in files:
            if file == 'Makefile':
                makefile_path = os.path.join(subdir, file)
                used_paths = parse_makefile(makefile_path, verilog_files)
                for key, paths in used_paths.items():
                    if key in results:
                        results[key].extend(paths)
                    else:
                        results[key] = paths
    
    # Write to CSV for used paths
    if args.used_path:
        with open(args.used_path, 'w') as csv_file:
            for key, paths in results.items():
                csv_file.write(f"{key},{','.join(paths)}\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-p', '--path', required=True, help='Path to start searching from')
    parser.add_argument('-o', '--output', help='Output CSV file', default='output.csv')
    parser.add_argument('-vp', '--verilog_path', help='Path to list all .sv files')
    parser.add_argument('-u', '--used_path', help='Output CSV file for used paths')
    args = parser.parse_args()

    main(args)