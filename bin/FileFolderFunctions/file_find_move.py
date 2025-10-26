# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FileFindMove
# Purpose: Initializes the FileFindMove class.
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

import os
import re
import shutil
import subprocess


class FileFindMove:
    def __init__(self, root_dir, regex_list):
        """
        Initializes the FileFindMove class.

        Args:
            root_dir (str): Root directory to start searching from (relative to the repo root).
            regex_list (list): List of [search, replace] regex pairs.
        """
        # Determine the repository root
        self.repo_root = subprocess.check_output(
            ['git', 'rev-parse', '--show-toplevel']
        ).strip().decode('utf-8')

        # Root directory to search, relative to the repository root
        self.root_dir = os.path.join(self.repo_root, root_dir)
        self.regex_list = regex_list  # List of [search, replace] regex pairs

        # Lists to track files and directories
        self.src_file_list = []  # Files matching the regex
        self.dst_file_list = []  # Destination paths for files
        self.src_dir_list = []  # Directories matching the regex
        self.dst_dir_list = []  # Destination paths for directories

    def find_items(self):
        """
        Recursively searches for files and directories in self.root_dir matching any of the regex patterns
        and populates self.src_file_list, self.dst_file_list, self.src_dir_list, and self.dst_dir_list.
        """
        if not os.path.exists(self.root_dir):
            raise FileNotFoundError(f"Root directory '{self.root_dir}' does not exist.")

        # Walk through the root directory recursively
        for root, dirs, files in os.walk(self.root_dir, topdown=True):
            # Check directories first
            for dirname in dirs:
                dir_path = os.path.relpath(os.path.join(root, dirname), self.repo_root)
                for search, replace in self.regex_list:
                    if re.search(search, dir_path):
                        self.src_dir_list.append(dir_path)
                        dst_path = re.sub(search, replace, dir_path)
                        self.dst_dir_list.append(dst_path)
                        break  # Avoid duplicate entries for the same directory

            # Check files
            for filename in files:
                file_path = os.path.relpath(os.path.join(root, filename), self.repo_root)
                for search, replace in self.regex_list:
                    if re.search(search, file_path):
                        self.src_file_list.append(file_path)
                        dst_path = re.sub(search, replace, file_path)
                        self.dst_file_list.append(dst_path)
                        break  # Avoid duplicate entries for the same file

    def _move_directories(self):
        """
        Moves directories from the source list to their corresponding destination paths,
        ensuring no redundant hierarchies are created. Dynamically updates the source
        paths of leaf directories and files as parent directories are moved.
        """
        if not self.src_dir_list or not self.dst_dir_list:
            print("No directories to move. Did you call find_items()?")
            return

        # Sort directories by depth (shallowest first)
        dir_moves = sorted(zip(self.src_dir_list, self.dst_dir_list), key=lambda pair: pair[0].count(os.sep))

        for src, dst in dir_moves:
            src_path = os.path.join(self.repo_root, src)
            dst_path = os.path.join(self.repo_root, dst)

            # Ensure destination parent directory exists
            os.makedirs(os.path.dirname(dst_path), exist_ok=True)

            # Move the directory
            if os.path.isdir(src_path):
                shutil.move(src_path, dst_path)
                print(f"Moved Directory: '{src_path}' -> '{dst_path}'")

                # Update all remaining source paths (directories and files)
                self._update_paths(src, dst)
            else:
                print(f"Skipping (Directory Not Found): '{src_path}'")

    def _update_paths(self, old_path, new_path):
        """
        Updates the source paths for directories and files to reflect the new base path after a directory move.

        Args:
            old_path (str): The old path of the directory that was moved (relative to repo_root).
            new_path (str): The new path of the directory (relative to repo_root).
        """
        # Update directory paths
        self.src_dir_list = [
            path.replace(old_path, new_path, 1) if path.startswith(old_path + os.sep) else path
            for path in self.src_dir_list
        ]
        self.dst_dir_list = [
            path.replace(old_path, new_path, 1) if path.startswith(old_path + os.sep) else path
            for path in self.dst_dir_list
        ]

        # Update file paths
        self.src_file_list = [
            path.replace(old_path, new_path, 1) if path.startswith(old_path + os.sep) else path
            for path in self.src_file_list
        ]
        self.dst_file_list = [
            path.replace(old_path, new_path, 1) if path.startswith(old_path + os.sep) else path
            for path in self.dst_file_list
        ]

    def _move_files(self):
        """
        Moves files from the source list to their corresponding destination paths,
        ensuring that file moves are handled after directory moves.
        """
        if not self.src_file_list or not self.dst_file_list:
            print("No files to move. Did you call find_items()?")
            return

        for src, dst in zip(self.src_file_list, self.dst_file_list):
            src_path = os.path.join(self.repo_root, src)
            dst_path = os.path.join(self.repo_root, dst)

            # Ensure destination directory exists
            os.makedirs(os.path.dirname(dst_path), exist_ok=True)

            # Move the file
            if os.path.isfile(src_path):
                shutil.move(src_path, dst_path)
                print(f"Moved File: '{src_path}' -> '{dst_path}'")
            else:
                print(f"Skipping (File Not Found): '{src_path}'")

    def move_items(self):
        """
        Executes the move operation for directories and files, ensuring correct order.
        """
        print("Moving directories...")
        self._move_directories()
        print("Moving files...")
        self._move_files()


    def report_items(self, filename):
        """
        Reports the source and destination lists to an output file.

        Args:
            filename (str): Name of the output file.
        """
        with open(filename, 'w') as f:
            f.write("Matched Files Report:\n")
            f.write("=" * 50 + "\n")
            for src, dst in zip(self.src_file_list, self.dst_file_list):
                f.write(f"File Source: {src}\n")
                f.write(f"File Destination: {dst}\n")
                f.write("-" * 50 + "\n")

            f.write("\nMatched Directories Report:\n")
            f.write("=" * 50 + "\n")
            for src, dst in zip(self.src_dir_list, self.dst_dir_list):
                f.write(f"Directory Source: {src}\n")
                f.write(f"Directory Destination: {dst}\n")
                f.write("-" * 50 + "\n")

        print(f"Report written to {filename}")


