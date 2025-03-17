import argparse
from pathlib import Path

def print_tree(directory, prefix="", exclude_dirs=None, exclude_files=None):
    """Recursively prints directory structure like the UNIX `tree` command."""
    exclude_dirs = set(exclude_dirs or [])
    exclude_files = set(exclude_files or [])

    # Get all items, filtering out excluded ones
    items = sorted([p for p in directory.iterdir() if p.name not in exclude_dirs and p.name not in exclude_files])

    for index, item in enumerate(items):
        connector = "└── " if index == len(items) - 1 else "├── "
        print(prefix + connector + item.name)

        # If item is a directory, recurse
        if item.is_dir():
            extension = "    " if index == len(items) - 1 else "│   "
            print_tree(item, prefix + extension, exclude_dirs, exclude_files)

def main():
    parser = argparse.ArgumentParser(description="Custom Python Tree Command")
    parser.add_argument("--path", type=str, required=True, help="Root directory to display")
    parser.add_argument("--exclude-dir", type=str, nargs="*", default=[], help="Directories to exclude")
    parser.add_argument("--exclude-file", type=str, nargs="*", default=[], help="Files to exclude")
    
    args = parser.parse_args()
    root_dir = Path(args.path)

    if not root_dir.exists() or not root_dir.is_dir():
        print(f"Error: '{args.path}' is not a valid directory.")
        return

    # print(root_dir.resolve())  # Print root path like `tree` does
    print(root_dir)
    print_tree(root_dir, "", args.exclude_dir, args.exclude_file)

if __name__ == "__main__":
    main()

