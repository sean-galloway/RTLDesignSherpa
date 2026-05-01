#!/bin/bash
# Re-roll bitstream + program + run baseline DMA.
# Source me from this directory: `. cmds.sh`

set -e

# Per-flow output directories (kept clean of cross-flow contamination).
mkdir -p csv build
LOG=build/run.log
rm -f "$LOG"
touch "$LOG"

echo "=== make clean-all + make bitstream (re-roll P&R) ==="            | tee -a "$LOG"
make clean-all >> "$LOG" 2>&1
make bitstream >> "$LOG" 2>&1
echo "bitstream done"                                               | tee -a "$LOG"

echo "=== post-route timing summary ==="                            | tee -a "$LOG"
grep -A3 "WNS(ns)" reports/timing_summary.txt | head -5             | tee -a "$LOG"

echo "=== make program ==="                                         | tee -a "$LOG"
make program >> "$LOG" 2>&1
echo "program done"                                                 | tee -a "$LOG"

UART_PORT=/dev/serial/by-id/usb-Digilent_Digilent_USB_Device_210292B7D46F-if01-port0

# ---- Per-sweep knobs ------------------------------------------------------
# Edit these for each sweep. The CSV name is the only state shared across
# the loop iterations — a fresh CSV per sweep keeps each experiment's data
# separate and ready to plot independently.
SWEEP_CHANNELS=1
SWEEP_DESCRIPTORS=1
SWEEP_SIZE=512KB
SWEEP_CSV=csv/results_${SWEEP_DESCRIPTORS}desc_${SWEEP_CHANNELS}ch_${SWEEP_SIZE}.csv

# Start each sweep with a clean CSV so the header is written exactly once.
rm -f "$SWEEP_CSV"

# Wider sweep to capture the pipelined-delay-model cliff:
# engines run AR/AW_MAX_OUTSTANDING=8 × ~16-beat bursts → ~128 beats in flight,
# so throughput stays flat up to ~128 cycles of memory latency, then degrades.
# The points cluster around the predicted cliff at L=128 to map it cleanly.
echo "=== response-delay sweep ${SWEEP_DESCRIPTORS}desc_${SWEEP_CHANNELS}ch_${SWEEP_SIZE} (delay 0..256) ===" | tee -a "$LOG"
echo "    accumulating results into ${SWEEP_CSV}"                                    | tee -a "$LOG"
for d in 0 32 64 96 112 128 144 160 192 224 256; do
    echo ""                                                                          | tee -a "$LOG"
    echo "--- RESP_DELAY = ${d} cycles (rd=wr) ---"                                  | tee -a "$LOG"
    python3 host/characterize.py \
        --port "$UART_PORT" \
        --channels "$SWEEP_CHANNELS" \
        --descriptors "$SWEEP_DESCRIPTORS" \
        --size "$SWEEP_SIZE" \
        --rd-delay "$d" --wr-delay "$d" \
        --output "$SWEEP_CSV" \
        -v >> "$LOG" 2>&1 || true
done

echo ""                                                                              | tee -a "$LOG"
echo "=== sweep CSV (${SWEEP_CSV}) ==="                                              | tee -a "$LOG"
column -s, -t "$SWEEP_CSV" 2>/dev/null | tee -a "$LOG"

echo ""                                                                              | tee -a "$LOG"
echo "=== done — last 30 lines of ${LOG} ==="                                        | tee -a "$LOG"
tail -30 "$LOG"
