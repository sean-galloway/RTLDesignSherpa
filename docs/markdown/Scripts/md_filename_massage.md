<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

**[← Back to Scripts Index](index.md)**

# md_filename_massage

The `md_filename_massage` script at `bin/md_filename_massage.py` is a file renaming utility that recursively traverses a directory tree and renames files by prefixing them with their directory path structure, using underscores as separators. This is particularly useful for organizing documentation files where the directory hierarchy needs to be encoded in the filename itself.

## Overview

This script provides an automated way to rename files based on their location in the directory tree. For example, a file at `docs/scripts/utilities/helper.md` would be renamed to `scripts_utilities_helper.md`. The script includes safeguards to prevent duplicate renames and supports dry-run mode for previewing changes before applying them.

## Usage

The script provides command-line options for controlling the renaming behavior:

```bash
python3 bin/md_filename_massage.py [root_directory] [--dry-run] [--file-extensions ext1,ext2]
```

### Command-Line Options

- `root_directory` (optional): Root directory to process. Defaults to current directory if not specified.

- `--dry-run`: Show what would be renamed without actually renaming files. Useful for previewing changes before committing to them.

- `--file-extensions`: Comma-separated list of file extensions to process (e.g., "md,txt,py"). If not specified, all files are processed.

## Examples

### Basic Usage

Rename all files in the CocoTBFramework directory:
```bash
python3 bin/md_filename_massage.py CocoTBFramework
```

### Dry Run Mode

Preview changes without modifying files:
```bash
python3 bin/md_filename_massage.py CocoTBFramework --dry-run
```

### Filter by Extension

Process only markdown and text files:
```bash
python3 bin/md_filename_massage.py CocoTBFramework --file-extensions md,txt
```

### Process Current Directory

Process current directory with specific extensions:
```bash
python3 bin/md_filename_massage.py . --file-extensions md
```

## Features

### Smart Duplicate Detection

The script checks if a filename already has the correct directory prefix and skips it if so. This prevents redundant renaming operations.

### Extension Filtering

Control which file types are processed using the `--file-extensions` parameter. Extensions are case-insensitive and automatically normalized (leading dots are removed).

### Safe Operation

- Checks if target files already exist before renaming
- Provides detailed output showing old and new filenames
- Dry-run mode allows safe preview of operations
- Preserves file contents (only renames, never modifies)

### Path Handling

- Handles both absolute and relative paths
- Properly resolves symlinks and relative references
- Works across different directory depths

## Internal Functionality

### File Detection (`should_rename_file`)

Determines if a file should be renamed based on its extension. If no extension filter is specified, all files are processed.

### Filename Generation (`generate_new_filename`)

Generates the new filename by:
1. Computing the relative path from the root directory
2. Extracting directory components (excluding the filename itself)
3. Joining directory parts with underscores
4. Prepending the path prefix to the original filename
5. Checking if the prefix already exists to avoid duplicate prefixing

### File Discovery (`find_files_to_rename`)

Recursively walks the directory tree using `Path.rglob('*')` to find all files matching the extension filter. Returns a list of tuples containing `(current_path, new_filename)` for each file that needs renaming.

### Renaming Operation (`rename_files`)

Performs the actual renaming operation:
1. Validates that target files don't already exist (prevents overwrites)
2. Uses `Path.rename()` for atomic file system operations
3. Provides detailed progress output with checkmarks for success
4. Handles errors gracefully with informative messages

### Argument Parsing (`parse_file_extensions`)

Parses the comma-separated extension string, normalizing each extension by:
- Stripping whitespace
- Removing leading dots
- Converting to lowercase
- Filtering out empty values

## Output Format

The script provides clear, formatted output showing:
- Total number of files to be renamed
- For each file:
  - Original path (relative to current working directory)
  - New path with arrow indicator (`->`)
  - Success/failure status with visual indicators (checkmarks, X marks)
  - Warning messages for conflicts or errors

### Example Output

```
Processing directory: /path/to/project/CocoTBFramework
File extensions filter: md
Mode: Dry run

DRY RUN - Found 3 files to rename:

  CocoTBFramework/components/utilities/helper.md
  -> CocoTBFramework/components_utilities_helper.md
  (Would rename)

  CocoTBFramework/docs/examples/usage.md
  -> CocoTBFramework/docs_examples_usage.md
  (Would rename)

Dry run complete. 3 files would be renamed.
Run without --dry-run to perform the actual renaming.
```

## Error Handling

The script handles several error conditions:

1. **Non-existent directory**: Exits with error message if root directory doesn't exist
2. **Invalid directory**: Exits with error if path is not a directory
3. **Target file exists**: Skips renaming with warning message
4. **Permission errors**: Catches and reports file system permission issues
5. **General exceptions**: Provides informative error messages for unexpected conditions

## Use Cases

### Documentation Organization

When documentation is organized hierarchically but needs to be flattened (e.g., for a single-directory output), this script encodes the directory structure in filenames.

### Build System Integration

Useful in build systems where intermediate files from different directories need unique names when copied to a common output directory.

### Version Control Cleanup

Before migrating files to a new repository structure, encode the old structure in filenames to preserve context.

### Testing Frameworks

When test outputs from different modules need to be collected in a single directory without name collisions.

## Dependencies

The script uses only Python standard library modules:
- `os` - Operating system interfaces
- `sys` - System-specific parameters and functions
- `argparse` - Command-line argument parsing
- `pathlib.Path` - Object-oriented filesystem paths
- `typing` - Type hints for better code documentation

No external dependencies are required.

## Code Structure

The script follows a clean, modular design:

1. **Helper Functions**: Small, focused functions for specific tasks (filtering, generation, parsing)
2. **Main Functions**: Higher-level orchestration of the renaming process
3. **Argument Parsing**: Comprehensive CLI interface with help documentation
4. **Main Entry Point**: Coordinates the overall workflow with error handling

---

[Back to Scripts Index](index.md)

---
