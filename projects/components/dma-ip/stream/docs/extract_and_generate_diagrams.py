#!/usr/bin/env python3
"""
Extract Mermaid Diagrams, Generate PNGs, and Update Markdown

This script:
1. Scans markdown files for embedded Mermaid diagrams
2. Extracts each diagram to a separate .mmd file in assets/mermaid/
3. Generates PNG from each .mmd file using mmdc (Mermaid CLI)
4. Updates markdown files to reference PNGs instead of embedded Mermaid

Usage:
    python3 extract_and_generate_diagrams.py [--backup]

Requirements:
    - @mermaid-js/mermaid-cli (npm install -g @mermaid-js/mermaid-cli)
"""

import os
import re
import subprocess
import argparse
from pathlib import Path
import shutil
import json


def generate_diagram_id(md_file, line_num):
    """
    Generate a unique ID for a diagram based on file and position.

    Returns:
        String like "02_scheduler_L025" for line 25 in 02_scheduler.md
    """
    base_name = Path(md_file).stem  # e.g., "02_scheduler"
    return f"{base_name}_L{line_num:03d}"


def extract_mermaid_blocks(md_file):
    """
    Extract all Mermaid code blocks from a markdown file.

    Returns:
        List of tuples: [(diagram_content, line_number), ...]
    """
    with open(md_file, 'r', encoding='utf-8') as f:
        content = f.read()

    # Pattern to match ```mermaid ... ``` blocks
    pattern = r'```mermaid\n(.*?)```'
    matches = re.finditer(pattern, content, re.DOTALL)

    diagrams = []
    for match in matches:
        diagram = match.group(1).strip()
        # Calculate line number
        line_num = content[:match.start()].count('\n') + 1
        diagrams.append((diagram, line_num))

    return diagrams


def save_mermaid_file(diagram_content, mermaid_dir, diagram_id):
    """
    Save Mermaid diagram content to a .mmd file.

    Returns:
        Path to the saved .mmd file
    """
    mmd_file = mermaid_dir / f"{diagram_id}.mmd"
    with open(mmd_file, 'w', encoding='utf-8') as f:
        f.write(diagram_content)
    return mmd_file


def convert_mermaid_to_png(mmd_file, output_png, width=1200, background='white'):
    """
    Convert Mermaid .mmd file to PNG using mmdc (Mermaid CLI).

    Args:
        mmd_file: Path to .mmd source file
        output_png: Path to output PNG file
        width: Image width in pixels (default: 1200)
        background: Background color (default: 'white')

    Returns:
        True if successful, False otherwise
    """
    try:
        # Create Puppeteer config to disable sandbox (needed in containers)
        puppeteer_config = {
            "args": ["--no-sandbox", "--disable-setuid-sandbox"]
        }
        puppeteer_config_file = '/tmp/puppeteer-config.json'
        with open(puppeteer_config_file, 'w') as f:
            json.dump(puppeteer_config, f)

        # Run mmdc command
        cmd = [
            'mmdc',
            '-i', str(mmd_file),
            '-o', str(output_png),
            '-w', str(width),
            '-b', background,
            '--quiet',
            '-p', puppeteer_config_file
        ]

        result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)

        if result.returncode != 0:
            print(f"  ERROR: mmdc failed with code {result.returncode}")
            if result.stderr:
                print(f"  stderr: {result.stderr}")
            return False

        return True

    except subprocess.TimeoutExpired:
        print(f"  ERROR: mmdc timed out after 30 seconds")
        return False
    except FileNotFoundError:
        print(f"  ERROR: mmdc not found. Install with: npm install -g @mermaid-js/mermaid-cli")
        return False


def update_markdown_with_png_refs(md_file, diagram_info, backup=True):
    """
    Update markdown file to replace Mermaid blocks with PNG image references.

    Args:
        md_file: Path to markdown file
        diagram_info: List of tuples [(diagram_id, line_num), ...]
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

    # Pattern to match ```mermaid ... ``` blocks
    pattern = r'```mermaid\n(.*?)```'

    replacements = 0
    offset = 0

    for match in re.finditer(pattern, content, re.DOTALL):
        # Calculate line number
        line_num = content[:match.start()].count('\n') + 1

        # Find corresponding diagram ID
        diagram_id = None
        for did, dline in diagram_info:
            if dline == line_num:
                diagram_id = did
                break

        if not diagram_id:
            print(f"  WARNING: No diagram ID found for line {line_num}")
            continue

        # Create image reference
        # PNG in assets/images/, relative path from ch02_blocks/
        png_filename = f"{diagram_id}.png"
        mmd_filename = f"{diagram_id}.mmd"
        relative_png_path = f"../assets/images/{png_filename}"
        relative_mmd_path = f"../assets/mermaid/{mmd_filename}"

        # Create replacement text with PNG ref and link to source .mmd
        replacement = f'''![Diagram]({relative_png_path})

**Source:** [{mmd_filename}]({relative_mmd_path})'''

        # Replace in content
        start_pos = match.start() + offset
        end_pos = match.end() + offset
        content = content[:start_pos] + replacement + content[end_pos:]

        # Adjust offset for next replacement
        offset += len(replacement) - (match.end() - match.start())

        replacements += 1

    # Write modified content
    if replacements > 0:
        with open(md_file, 'w', encoding='utf-8') as f:
            f.write(content)

    return replacements


def process_markdown_file(md_file, mermaid_dir, images_dir, backup=True, verbose=True):
    """
    Process a single markdown file: extract Mermaid, generate PNGs, update markdown.

    Returns:
        Tuple: (mermaid_files_created, png_files_created, replacements_made)
    """
    if verbose:
        print(f"\nProcessing: {Path(md_file).name}")

    # Extract Mermaid blocks
    diagrams = extract_mermaid_blocks(md_file)

    if not diagrams:
        if verbose:
            print(f"  No Mermaid diagrams found")
        return (0, 0, 0)

    if verbose:
        print(f"  Found {len(diagrams)} Mermaid diagram(s)")

    mermaid_files = []
    png_files = []
    diagram_info = []  # [(diagram_id, line_num), ...]

    for idx, (diagram, line_num) in enumerate(diagrams, 1):
        # Generate unique ID
        diagram_id = generate_diagram_id(md_file, line_num)
        diagram_info.append((diagram_id, line_num))

        # Save Mermaid source file
        mmd_file = save_mermaid_file(diagram, mermaid_dir, diagram_id)
        mermaid_files.append(mmd_file)

        if verbose:
            print(f"  [{idx}/{len(diagrams)}] Saved: {mmd_file.name}")

        # Generate PNG
        output_png = images_dir / f"{diagram_id}.png"
        success = convert_mermaid_to_png(mmd_file, output_png)

        if success:
            png_files.append(output_png)
            if verbose:
                print(f"      Generated: {output_png.name}")
        else:
            if verbose:
                print(f"      Failed to generate PNG for {diagram_id}")

    # Update markdown file with PNG references
    replacements = update_markdown_with_png_refs(md_file, diagram_info, backup=backup)

    if verbose:
        print(f"  Updated {replacements} diagram reference(s) in markdown")

    return (len(mermaid_files), len(png_files), replacements)


def main():
    parser = argparse.ArgumentParser(
        description='Extract Mermaid diagrams, generate PNGs, and update markdown files'
    )
    parser.add_argument(
        '--backup',
        action='store_true',
        help='Create .bak backup files before modifying markdown'
    )
    parser.add_argument(
        '--no-backup',
        action='store_true',
        help='Do not create backup files (default: create backups)'
    )
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Suppress verbose output'
    )

    args = parser.parse_args()

    # Default to creating backups unless --no-backup specified
    create_backup = not args.no_backup

    # Get script directory (should be in docs/)
    script_dir = Path(__file__).parent
    docs_dir = script_dir / 'stream_spec' / 'ch02_blocks'
    mermaid_dir = script_dir / 'stream_spec' / 'assets' / 'mermaid'
    images_dir = script_dir / 'stream_spec' / 'assets' / 'images'

    if not docs_dir.exists():
        print(f"ERROR: Documentation directory not found: {docs_dir}")
        return 1

    # Create output directories
    mermaid_dir.mkdir(parents=True, exist_ok=True)
    images_dir.mkdir(parents=True, exist_ok=True)

    print(f"Extracting Mermaid diagrams and generating PNGs")
    print(f"Source directory: {docs_dir}")
    print(f"Mermaid output: {mermaid_dir}")
    print(f"PNG output: {images_dir}")
    print(f"Backup: {'Yes' if create_backup else 'No'}")
    print()

    # Find all markdown files in ch02_blocks/
    md_files = sorted(docs_dir.glob('*.md'))

    if not md_files:
        print(f"ERROR: No markdown files found in {docs_dir}")
        return 1

    print(f"Found {len(md_files)} markdown file(s)")

    total_mermaid = 0
    total_png = 0
    total_replacements = 0
    files_processed = 0

    for md_file in md_files:
        mermaid_count, png_count, replacements = process_markdown_file(
            md_file, mermaid_dir, images_dir,
            backup=create_backup, verbose=not args.quiet
        )

        if mermaid_count > 0:
            files_processed += 1
            total_mermaid += mermaid_count
            total_png += png_count
            total_replacements += replacements

    print(f"\n{'='*60}")
    print(f"Processing complete!")
    print(f"Files processed: {files_processed}")
    print(f"Mermaid source files created: {total_mermaid}")
    print(f"PNG files generated: {total_png}")
    print(f"Markdown replacements: {total_replacements}")
    print(f"{'='*60}")

    if create_backup:
        print(f"\nBackup files created with .bak extension")
        print(f"To restore: mv file.md.bak file.md")

    # List generated files
    print(f"\nMermaid source files: {mermaid_dir}")
    mmd_files = sorted(mermaid_dir.glob('*.mmd'))
    for mmd in mmd_files:
        print(f"  - {mmd.name}")

    print(f"\nPNG files: {images_dir}")
    png_files = sorted(images_dir.glob('*.png'))
    for png in png_files:
        print(f"  - {png.name}")

    return 0


if __name__ == '__main__':
    exit(main())
