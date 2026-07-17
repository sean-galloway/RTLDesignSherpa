#!/usr/bin/env python3
"""
Replace Mermaid code blocks with PNG image references in markdown files.

This script modifies markdown files to replace Mermaid diagrams with
references to the corresponding PNG files in the images/ directory.

Usage:
    python3 replace_mermaid_with_png.py [--backup]
"""

import os
import re
import argparse
from pathlib import Path
import shutil


def generate_diagram_id(md_file, line_num):
    """
    Generate the PNG filename for a diagram.

    Returns:
        String like "02_scheduler_L045.png"
    """
    base_name = Path(md_file).stem
    return f"{base_name}_L{line_num:03d}.png"


def replace_mermaid_with_png(md_file, images_dir, backup=True):
    """
    Replace Mermaid code blocks in a markdown file with PNG image references.

    Args:
        md_file: Path to markdown file
        images_dir: Path to images directory (relative to md_file)
        backup: If True, create .bak backup file

    Returns:
        Number of replacements made
    """
    with open(md_file, 'r', encoding='utf-8') as f:
        content = f.read()

    # Create backup if requested
    if backup:
        backup_file = str(md_file) + '.bak'
        shutil.copy2(md_file, backup_file)
        print(f"  Created backup: {Path(backup_file).name}")

    # Pattern to match ```mermaid ... ``` blocks with line tracking
    pattern = r'```mermaid\n(.*?)```'

    replacements = 0
    offset = 0

    for match in re.finditer(pattern, content, re.DOTALL):
        # Calculate line number
        line_num = content[:match.start()].count('\n') + 1

        # Generate PNG filename
        png_filename = generate_diagram_id(md_file, line_num)
        png_path = Path(images_dir) / png_filename

        # Check if PNG exists
        if not png_path.exists():
            print(f"  WARNING: PNG not found: {png_path}")
            continue

        # Create image reference
        # Use relative path from markdown file location
        relative_path = f"../images/{png_filename}"

        # Create replacement text with both PNG and original Mermaid (commented)
        diagram_content = match.group(1).strip()
        replacement = f'''![Diagram]({relative_path})

<!--
Original Mermaid diagram (for editing):

```mermaid
{diagram_content}
```
-->'''

        # Replace in content
        start_pos = match.start() + offset
        end_pos = match.end() + offset
        content = content[:start_pos] + replacement + content[end_pos:]

        # Adjust offset for next replacement
        offset += len(replacement) - (match.end() - match.start())

        replacements += 1
        print(f"  [{replacements}] Line {line_num} → {png_filename}")

    # Write modified content
    if replacements > 0:
        with open(md_file, 'w', encoding='utf-8') as f:
            f.write(content)

    return replacements


def main():
    parser = argparse.ArgumentParser(
        description='Replace Mermaid diagrams with PNG image references'
    )
    parser.add_argument(
        '--backup',
        action='store_true',
        help='Create .bak backup files before modifying'
    )
    parser.add_argument(
        '--no-backup',
        action='store_true',
        help='Do not create backup files (default: create backups)'
    )

    args = parser.parse_args()

    # Default to creating backups unless --no-backup specified
    create_backup = not args.no_backup

    # Get paths
    script_dir = Path(__file__).parent
    docs_dir = script_dir / 'stream_spec' / 'ch02_blocks'
    images_dir = script_dir / 'images'

    if not docs_dir.exists():
        print(f"ERROR: Documentation directory not found: {docs_dir}")
        return 1

    if not images_dir.exists():
        print(f"ERROR: Images directory not found: {images_dir}")
        return 1

    print(f"Replacing Mermaid diagrams with PNG references")
    print(f"Source directory: {docs_dir}")
    print(f"Images directory: {images_dir}")
    print(f"Backup: {'Yes' if create_backup else 'No'}")
    print()

    # Find all markdown files
    md_files = sorted(docs_dir.glob('*.md'))

    if not md_files:
        print(f"ERROR: No markdown files found in {docs_dir}")
        return 1

    total_replacements = 0
    files_modified = 0

    for md_file in md_files:
        print(f"Processing: {md_file.name}")

        replacements = replace_mermaid_with_png(md_file, images_dir, backup=create_backup)

        if replacements > 0:
            files_modified += 1
            total_replacements += replacements
        else:
            print(f"  No Mermaid diagrams to replace")

    print(f"\n{'='*60}")
    print(f"Replacement complete!")
    print(f"Files modified: {files_modified}")
    print(f"Total replacements: {total_replacements}")
    print(f"{'='*60}")

    if create_backup:
        print(f"\nBackup files created with .bak extension")
        print(f"To restore: mv file.md.bak file.md")

    return 0


if __name__ == '__main__':
    exit(main())
