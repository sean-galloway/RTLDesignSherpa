#!/bin/bash
################################################################################
# DMA Performance Analysis - Master Run Script
#
# This script runs comprehensive performance analysis for the DMA model,
# generating detailed analysis data (CSV) and visualizations (PNG).
#
# Directory Structure:
#   bin/                    - All Python scripts and packages
#   csv/                    - Generated CSV data files
#   assets/                 - Generated PNG visualization files
#   reports/                - Generated markdown reports
#
# Usage:
#   ./run_analysis.sh                    # Run comprehensive analysis (default)
#   ./run_analysis.sh --quick            # Quick mode (faster, less detail)
#   ./run_analysis.sh --help             # Show this help
#
################################################################################

set -e  # Exit on error

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Change to script directory
cd "$(dirname "$0")"

echo -e "${BLUE}╔════════════════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║          DMA Performance Analysis - Comprehensive Suite               ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════════════════════════════╝${NC}"
echo ""

################################################################################
# COMPREHENSIVE ANALYSIS (DEFAULT - ACTIVE)
################################################################################
# Performs complete READ and WRITE path analysis with all payload sizes.
# Generates detailed CSV reports and comprehensive visualizations.
#
# Outputs:
#   csv/analysis_read_path.csv           - READ path data
#   csv/analysis_write_path.csv          - WRITE path data
#   assets/payload_sweep_separate.png    - READ vs WRITE bandwidth plots
#
echo -e "${GREEN}[1/3] Running Comprehensive Analysis...${NC}"
python3 bin/comprehensive_analysis.py --save-csv --visualize \
    --payloads 256 512 1024 2048 \
    --channels 16

################################################################################
# OPTIMIZATION PLOTS GENERATION (DEFAULT - ACTIVE)
################################################################################
# Creates detailed visualizations showing optimization effects:
# - Waterfall chart of incremental optimizations
# - Bottleneck analysis across payloads and pipeline depths
# - SRAM vs performance tradeoffs
# - WRITE path independent analysis
#
# Outputs:
#   assets/optimization_waterfall.png    - Step-by-step optimization effects
#   assets/bottleneck_analysis.png       - Pipeline depth analysis
#   assets/sram_vs_performance.png       - SRAM cost-benefit curves
#   assets/write_path_analysis.png       - WRITE path detailed analysis
#
echo -e "${GREEN}[2/3] Generating Optimization Visualizations...${NC}"
python3 bin/generate_optimization_plots.py

################################################################################
# PAYLOAD SWEEP ANALYSIS (DEFAULT - ACTIVE)
################################################################################
# Sweeps all payload sizes (256B to 2KB) for both analytical and SimPy models.
# Validates that both models agree on performance across configurations.
#
# Outputs:
#   csv/payload_sweep_analytical.csv     - Analytical model results
#   csv/payload_sweep_simpy.csv          - SimPy simulation results
#
echo -e "${GREEN}[3/3] Running Payload Sweep Analysis...${NC}"
python3 bin/run_payload_sweep.py --analytical-only --save-csv \
    --payloads 256 512 1024 2048 \
    --channels 16

################################################################################
# ADDITIONAL ANALYSIS OPTIONS (COMMENTED OUT BY DEFAULT)
################################################################################
# Uncomment the sections below to run additional analyses.

## QUICK START EXAMPLES
## Runs individual examples showing different aspects of the model.
## Use: Understand specific features or validate single configurations.
# echo -e "${GREEN}Running Quick Start Examples...${NC}"
# python3 bin/quick_start.py all

## CLEAN ANALYSIS (READ and WRITE SEPARATE)
## Simple, focused analysis showing READ and WRITE paths independently.
## Use: Quick overview without full payload sweep.
# echo -e "${GREEN}Running Clean Analysis...${NC}"
# python3 bin/clean_analysis.py

## CONFIGURATION EXPLORER
## Interactive tool to explore different DMA configurations.
## Use: Experiment with parameters and see immediate results.
# echo -e "${GREEN}Running Configuration Explorer...${NC}"
# python3 bin/config_explorer.py --channels 16 --payload 2048 --pipeline 4 --streaming

## COMPLETE ANALYSIS WITH SIMPY VALIDATION
## Full analysis including SimPy discrete-event simulation for validation.
## WARNING: This is much slower (~5-10 minutes) than analytical-only mode.
## Use: When you need simulation validation of analytical results.
# echo -e "${GREEN}Running Complete Analysis (with SimPy)...${NC}"
# python3 bin/run_complete_analysis.py

## SIMPY MODEL VALIDATION
## Validates SimPy simulation against analytical model across multiple configs.
## Generates validation report showing agreement between models.
# echo -e "${GREEN}Running SimPy Validation...${NC}"
# python3 bin/simpy_model/validate.py
# # Outputs: csv/validation_report.csv

## SIMPY VS ANALYTICAL COMPARISON
## Channel sweep comparison with visualization plots.
## Generates comparison plots for baseline and optimized configurations.
# echo -e "${GREEN}Running Model Comparison...${NC}"
# python3 bin/simpy_model/compare.py
# # Outputs:
# #   csv/model_comparison.csv
# #   assets/comparison_baseline.png
# #   assets/comparison_optimized.png

## OPTIMIZATION SEQUENCE ANALYSIS
## Step-by-step analysis adding each optimization incrementally.
## Shows the impact of each optimization (pipelining, streaming, etc.).
# echo -e "${GREEN}Running Optimization Sequence...${NC}"
# python3 bin/simpy_model/optimizations.py
# # Outputs: csv/optimization_results.csv

## PAYLOAD SWEEP WITH SIMPY (SLOWER)
## Full payload sweep using both analytical AND SimPy simulation.
## WARNING: Much slower than analytical-only (5-10x longer runtime).
# echo -e "${GREEN}Running Full Payload Sweep (Analytical + SimPy)...${NC}"
# python3 bin/run_payload_sweep.py --save-csv \
#     --payloads 256 512 1024 2048 \
#     --channels 16
# # Outputs:
# #   csv/payload_sweep_analytical.csv
# #   csv/payload_sweep_simpy.csv

################################################################################
# CUSTOM CONFIGURATIONS
################################################################################
# Modify these commands for custom analysis scenarios.

## CUSTOM PAYLOAD SIZES
## Test specific payload sizes of interest.
# python3 bin/comprehensive_analysis.py --save-csv --visualize \
#     --payloads 512 1024 \
#     --channels 16

## CUSTOM CHANNEL COUNT
## Analyze different numbers of channels (e.g., 8 or 32 channels).
# python3 bin/comprehensive_analysis.py --save-csv --visualize \
#     --payloads 256 512 1024 2048 \
#     --channels 32

## QUICK MODE (FASTER)
## Run analysis with fewer data points for faster results.
# python3 bin/run_complete_analysis.py --quick --no-plots

################################################################################
# POST-ANALYSIS SUMMARY
################################################################################

echo ""
echo -e "${BLUE}╔════════════════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║                       Analysis Complete!                               ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════════════════════════════╝${NC}"
echo ""
echo -e "${GREEN}Generated Files:${NC}"
echo ""
echo -e "${YELLOW}CSV Data Files (csv/):${NC}"
echo "  • analysis_read_path.csv           - READ path analysis data"
echo "  • analysis_write_path.csv          - WRITE path analysis data"
echo "  • payload_sweep_analytical.csv     - Payload sweep results"
echo ""
echo -e "${YELLOW}Visualization Files (assets/):${NC}"
echo "  • payload_sweep_separate.png       - READ vs WRITE comparison"
echo "  • optimization_waterfall.png       - Optimization progression"
echo "  • bottleneck_analysis.png          - Pipeline depth analysis"
echo "  • sram_vs_performance.png          - SRAM cost-benefit"
echo "  • write_path_analysis.png          - WRITE path details"
echo ""
echo -e "${YELLOW}Key Findings:${NC}"
echo "  • READ path:  44 GB/s (baseline) → 57.6 GB/s (optimized) ✅"
echo "  • WRITE path: 20 GB/s (limited by 256B burst size) ❌"
echo "  • Target: 50 GB/s"
echo "  • READ meets target with pipelining (depth ≥ 2)"
echo "  • WRITE requires 2KB bursts to meet target"
echo ""
echo -e "${GREEN}Next Steps:${NC}"
echo "  • Review CSV files for detailed data"
echo "  • Examine PNG visualizations for insights"
echo "  • See OUTPUT_ORGANIZATION.md for file details"
echo "  • See README.md for additional analysis options"
echo ""
