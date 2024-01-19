#!/bin/bash

# Directory containing WaveDrom JSON files
SOURCE_DIR=$REPO_ROOT/docs/mark_down/rtl/_wavedrom

# Output directory for SVG files
OUTPUT_DIR=$REPO_ROOT/docs/mark_down/rtl/_wavedrom_svg

# Create output directory if it doesn't exist
mkdir -p "$OUTPUT_DIR"

# Loop through all .json files in the source directory
for file in "$SOURCE_DIR"/*.json; do
    filename=$(basename -- "$file")
    name="${filename%.*}"
    echo "Converting $file to SVG..."
    wavedrom-cli -i "$file" -s "$OUTPUT_DIR/$name.svg"
done

echo "Conversion complete."
