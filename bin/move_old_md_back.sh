#!/usr/bin/bash

# Directory of the repository
repo_dir="/home/sean/github/RTLDesignSherpa"

# Navigate to the repository directory
cd "$repo_dir"

# Find all .md.OLD.md files and process them
find . -name '*.md.OLD.md' | while read old_md; do
    # Construct the new .md filename
    # new_md="${old_md%.OLD.md}.md"
    new_md="${old_md%%.OLD.md}"

    # Check if the corresponding .md file exists
    if [ -f "$new_md" ]; then
        # Move the .md.OLD.md file to replace the .md file
        mv "$old_md" "$new_md"
        echo "Replaced $new_md"
    fi
done