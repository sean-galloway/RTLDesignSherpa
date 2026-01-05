#!/usr/bin/env python3
"""
update_doc_headers.py - Add/update common headers across markdown documentation.

Usage:
    ./bin/update_doc_headers.py                    # Preview changes (dry-run)
    ./bin/update_doc_headers.py --apply            # Apply changes
    ./bin/update_doc_headers.py --check            # Check which files need updates
    ./bin/update_doc_headers.py --remove           # Remove headers from all files

The header template is read from: docs/markdown/assets/doc_header.md

Directories processed:
    - docs/markdown/
    - projects/components/
"""

import argparse
from pathlib import Path

# Directories to process (relative to repo root)
DOC_DIRECTORIES = [
    'docs/markdown',
    'projects/components',
]

# Files to skip (basename matching)
SKIP_FILE_BASENAMES = {
    'overview.md',           # Main README has its own header
    'doc_header.md',         # The template itself
}

# Directories to skip (any path component matching)
SKIP_DIRS = {
    'assets',
    'local_sim_build',       # Generated simulation files
    'generated',             # Generated files
    '__pycache__',
    '.git',
}

# Header markers
HEADER_START = '<!-- RTL Design Sherpa Documentation Header -->'
HEADER_END = '<!-- End Header -->'


def load_header_template(repo_root: Path) -> str:
    """Load the header template from the assets directory."""
    template_path = repo_root / 'docs' / 'markdown' / 'assets' / 'doc_header.md'
    if not template_path.exists():
        raise FileNotFoundError(f"Header template not found: {template_path}")
    return template_path.read_text()


def has_header(content: str) -> bool:
    """Check if content already has the documentation header."""
    return HEADER_START in content


def extract_existing_header(content: str) -> tuple[str, str]:
    """Extract existing header and remaining content."""
    if not has_header(content):
        return '', content

    # Find header boundaries
    start_idx = content.find(HEADER_START)
    end_idx = content.find(HEADER_END)

    if end_idx == -1:
        # Malformed header - just remove from start marker
        return content[:start_idx], content[start_idx:]

    # Include the end marker and any trailing newlines
    end_idx = content.find('\n', end_idx)
    if end_idx == -1:
        end_idx = len(content)
    else:
        # Skip blank lines after header
        while end_idx < len(content) and content[end_idx] in '\n\r':
            end_idx += 1

    header = content[start_idx:end_idx]
    remaining = content[end_idx:].lstrip('\n')
    prefix = content[:start_idx].rstrip('\n')

    return header, (prefix + '\n\n' + remaining if prefix else remaining)


def add_header(content: str, header: str) -> str:
    """Add header to content, replacing existing if present."""
    if has_header(content):
        _, content = extract_existing_header(content)

    # Remove any leading whitespace from content
    content = content.lstrip('\n')

    return header.rstrip('\n') + '\n\n' + content


def remove_header(content: str) -> str:
    """Remove header from content if present."""
    if not has_header(content):
        return content

    _, content = extract_existing_header(content)
    return content


def should_skip_file(md_file: Path) -> bool:
    """Check if a file should be skipped."""
    # Skip by basename
    if md_file.name in SKIP_FILE_BASENAMES:
        return True

    # Skip by directory component
    for part in md_file.parts:
        if part in SKIP_DIRS:
            return True

    return False


def find_markdown_files(repo_root: Path) -> list[Path]:
    """Find all markdown files to process across all doc directories."""
    files = []

    for doc_dir_rel in DOC_DIRECTORIES:
        doc_dir = repo_root / doc_dir_rel
        if not doc_dir.exists():
            print(f"Warning: Directory not found: {doc_dir}")
            continue

        for md_file in doc_dir.rglob('*.md'):
            if should_skip_file(md_file):
                continue
            files.append(md_file)

    return sorted(files)


def main():
    parser = argparse.ArgumentParser(description='Update documentation headers')
    parser.add_argument('--apply', action='store_true',
                        help='Apply changes (default is dry-run)')
    parser.add_argument('--check', action='store_true',
                        help='Only check which files need updates')
    parser.add_argument('--remove', action='store_true',
                        help='Remove headers from all files')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Show detailed output')
    args = parser.parse_args()

    # Find repo root
    script_path = Path(__file__).resolve()
    repo_root = script_path.parent.parent

    # Load header template
    try:
        header_template = load_header_template(repo_root)
    except FileNotFoundError as e:
        print(f"Error: {e}")
        return 1

    # Find all markdown files
    md_files = find_markdown_files(repo_root)
    print(f"Found {len(md_files)} markdown files to process")
    print(f"Directories: {', '.join(DOC_DIRECTORIES)}\n")

    # Track statistics
    needs_update = []
    already_current = []
    updated = []
    errors = []

    for md_file in md_files:
        # Get relative path from repo root for display
        try:
            rel_path = md_file.relative_to(repo_root)
        except ValueError:
            rel_path = md_file

        try:
            content = md_file.read_text()

            if args.remove:
                if has_header(content):
                    new_content = remove_header(content)
                    if args.apply:
                        md_file.write_text(new_content)
                        updated.append(rel_path)
                        print(f"  Removed header: {rel_path}")
                    else:
                        needs_update.append(rel_path)
                        print(f"  Would remove header: {rel_path}")
                else:
                    already_current.append(rel_path)
                    if args.verbose:
                        print(f"  No header: {rel_path}")
            else:
                # Add/update header
                new_content = add_header(content, header_template)

                if content == new_content:
                    already_current.append(rel_path)
                    if args.verbose:
                        print(f"  Current: {rel_path}")
                elif args.check:
                    if has_header(content):
                        print(f"  Needs update: {rel_path}")
                    else:
                        print(f"  Missing header: {rel_path}")
                    needs_update.append(rel_path)
                elif args.apply:
                    md_file.write_text(new_content)
                    updated.append(rel_path)
                    if has_header(content):
                        print(f"  Updated: {rel_path}")
                    else:
                        print(f"  Added header: {rel_path}")
                else:
                    needs_update.append(rel_path)
                    if has_header(content):
                        print(f"  Would update: {rel_path}")
                    else:
                        print(f"  Would add header: {rel_path}")

        except Exception as e:
            errors.append((rel_path, str(e)))
            print(f"  Error: {rel_path}: {e}")

    # Summary
    print(f"\n{'='*50}")
    print("Summary:")
    if args.apply:
        print(f"  Updated: {len(updated)} files")
    else:
        print(f"  Would update: {len(needs_update)} files")
    print(f"  Already current: {len(already_current)} files")
    if errors:
        print(f"  Errors: {len(errors)} files")

    if not args.apply and needs_update:
        print(f"\nRun with --apply to make changes")

    return 0 if not errors else 1


if __name__ == '__main__':
    exit(main())
