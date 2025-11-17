#!/usr/bin/env python3
"""
Mermaid to PNG Converter for STREAM Documentation

This script extracts Mermaid diagrams from markdown files and converts them to PNG images
using the Mermaid CLI (mmdc). Generated PNGs are saved in an 'images/' subdirectory.

Usage:
    python3 convert_mermaid_to_png.py [--output-dir DIR]

Requirements:
    - @mermaid-js/mermaid-cli (npm install -g @mermaid-js/mermaid-cli)
"""

import os
import re
import subprocess
import argparse
from pathlib import Path
import tempfile
import hashlib


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
        # Calculate approximate line number
        line_num = content[:match.start()].count('\n') + 1
        diagrams.append((diagram, line_num))

    return diagrams


def generate_diagram_id(md_file, line_num):
    """
    Generate a unique ID for a diagram based on file and position.

    Returns:
        String like "02_scheduler_L45" for line 45 in 02_scheduler.md
    """
    base_name = Path(md_file).stem  # e.g., "02_scheduler"
    return f"{base_name}_L{line_num:03d}"


def convert_mermaid_to_png(mermaid_code, output_png, width=1200, background='white'):
    """
    Convert Mermaid code to PNG using mmdc (Mermaid CLI).

    Args:
        mermaid_code: String containing Mermaid diagram code
        output_png: Path to output PNG file
        width: Image width in pixels (default: 1200)
        background: Background color (default: 'white')

    Returns:
        True if successful, False otherwise
    """
    # Create temporary file for Mermaid code
    with tempfile.NamedTemporaryFile(mode='w', suffix='.mmd', delete=False) as tmp:
        tmp.write(mermaid_code)
        tmp_file = tmp.name

    try:
        # Run mmdc command
        # Note: --puppeteerConfigFile used for sandbox workaround in containers
        cmd = [
            'mmdc',
            '-i', tmp_file,
            '-o', str(output_png),
            '-w', str(width),
            '-b', background,
            '--quiet',
            '-p', '/tmp/puppeteer-config.json'  # Will create this config file
        ]

        # Create Puppeteer config to disable sandbox (needed in containers)
        puppeteer_config = {
            "args": ["--no-sandbox", "--disable-setuid-sandbox"]
        }
        with open('/tmp/puppeteer-config.json', 'w') as f:
            import json
            json.dump(puppeteer_config, f)

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
    finally:
        # Clean up temporary file
        if os.path.exists(tmp_file):
            os.remove(tmp_file)


def process_markdown_file(md_file, output_dir, verbose=True):
    """
    Process a single markdown file: extract Mermaid diagrams and convert to PNG.

    Returns:
        List of generated PNG file paths
    """
    if verbose:
        print(f"\nProcessing: {Path(md_file).name}")

    diagrams = extract_mermaid_blocks(md_file)

    if not diagrams:
        if verbose:
            print(f"  No Mermaid diagrams found")
        return []

    if verbose:
        print(f"  Found {len(diagrams)} Mermaid diagram(s)")

    generated_files = []

    for idx, (diagram, line_num) in enumerate(diagrams, 1):
        # Generate unique filename
        diagram_id = generate_diagram_id(md_file, line_num)
        output_png = output_dir / f"{diagram_id}.png"

        if verbose:
            print(f"  [{idx}/{len(diagrams)}] Converting diagram at line {line_num} → {output_png.name}")

        success = convert_mermaid_to_png(diagram, output_png)

        if success:
            generated_files.append(output_png)
            if verbose:
                print(f"      ✓ Generated: {output_png}")
        else:
            if verbose:
                print(f"      ✗ Failed to generate {output_png}")

    return generated_files


def main():
    parser = argparse.ArgumentParser(
        description='Convert Mermaid diagrams in markdown files to PNG images'
    )
    parser.add_argument(
        '--output-dir',
        type=str,
        default='images',
        help='Output directory for PNG files (default: images/)'
    )
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Suppress verbose output'
    )

    args = parser.parse_args()

    # Get script directory (should be in docs/)
    script_dir = Path(__file__).parent
    docs_dir = script_dir / 'stream_spec' / 'ch02_blocks'

    if not docs_dir.exists():
        print(f"ERROR: Documentation directory not found: {docs_dir}")
        return 1

    # Create output directory
    output_dir = script_dir / args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"Converting Mermaid diagrams to PNG")
    print(f"Source directory: {docs_dir}")
    print(f"Output directory: {output_dir}")

    # Find all markdown files in ch02_blocks/
    md_files = sorted(docs_dir.glob('*.md'))

    if not md_files:
        print(f"ERROR: No markdown files found in {docs_dir}")
        return 1

    print(f"Found {len(md_files)} markdown file(s)")

    all_generated = []

    for md_file in md_files:
        generated = process_markdown_file(md_file, output_dir, verbose=not args.quiet)
        all_generated.extend(generated)

    print(f"\n{'='*60}")
    print(f"Conversion complete!")
    print(f"Total diagrams converted: {len(all_generated)}")
    print(f"PNG files saved to: {output_dir}")
    print(f"{'='*60}")

    # List all generated files
    if all_generated:
        print("\nGenerated files:")
        for png_file in sorted(all_generated):
            print(f"  - {png_file.name}")

    return 0


if __name__ == '__main__':
    exit(main())
