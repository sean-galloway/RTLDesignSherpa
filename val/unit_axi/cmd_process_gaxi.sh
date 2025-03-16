#!/bin/bash

# Default log file
LOG_FILE=""

# Function to display usage
usage() {
    echo "Usage: $0 -l <logfile>"
    exit 1
}

# Parse command-line options
while getopts "l:" opt; do
    case ${opt} in
        l ) LOG_FILE=${OPTARG} ;;
        * ) usage ;;
    esac
done

# Ensure log file is provided and exists
if [[ -z "$LOG_FILE" || ! -f "$LOG_FILE" ]]; then
    echo "Error: Log file not specified or does not exist."
    usage
fi

# Extract transactions and store in respective files
egrep "write_master.*Transaction completed" "$LOG_FILE" | sed 's/.*DEBUG//' > wr_fail.txt
egrep "Write monitor.*Transaction received"   "$LOG_FILE" | sed 's/.*DEBUG//' > wr_mon_fail.txt
egrep "Read monitor.*Transaction received"    "$LOG_FILE" | sed 's/.*DEBUG//' > rd_mon_fail.txt
egrep "read_slave.*Transaction received"      "$LOG_FILE" | sed 's/.*DEBUG//' > rd_fail.txt

echo "Extraction complete. Processed logs are saved in:"
echo "  - wr_fail.txt"
echo "  - wr_mon_fail.txt"
echo "  - rd_mon_fail.txt"
echo "  - rd_fail.txt"

