#!/bin/bash
# Re-roll bitstream + program + run baseline DMA.
# Source me from this directory: `. cmds.sh`

set -e

rm -f run.log
touch run.log

echo "=== make clean-all + make bitstream (re-roll P&R) ==="            | tee -a run.log
make clean-all >> run.log 2>&1
make bitstream >> run.log 2>&1
echo "bitstream done"                                               | tee -a run.log

echo "=== post-route timing summary ==="                            | tee -a run.log
grep -A3 "WNS(ns)" reports/timing_summary.txt | head -5             | tee -a run.log

echo "=== make program ==="                                         | tee -a run.log
make program >> run.log 2>&1
echo "program done"                                                 | tee -a run.log

UART_PORT=/dev/serial/by-id/usb-Digilent_Digilent_USB_Device_210292B7D46F-if01-port0

# ---- Per-sweep knobs ------------------------------------------------------
# Edit these for each sweep. The CSV name is the only state shared across
# the loop iterations — a fresh CSV per sweep keeps each experiment's data
# separate and ready to plot independently.
SWEEP_CHANNELS=1
SWEEP_DESCRIPTORS=1
SWEEP_SIZE=512KB
SWEEP_CSV=results_${SWEEP_DESCRIPTORS}desc_${SWEEP_CHANNELS}ch_${SWEEP_SIZE}.csv

# Start each sweep with a clean CSV so the header is written exactly once.
rm -f "$SWEEP_CSV"

# Wider sweep to capture the pipelined-delay-model cliff:
# engines run AR/AW_MAX_OUTSTANDING=8 × ~16-beat bursts → ~128 beats in flight,
# so throughput stays flat up to ~128 cycles of memory latency, then degrades.
# The points cluster around the predicted cliff at L=128 to map it cleanly.
echo "=== response-delay sweep ${SWEEP_DESCRIPTORS}desc_${SWEEP_CHANNELS}ch_${SWEEP_SIZE} (delay 0..256) ===" | tee -a run.log
echo "    accumulating results into ${SWEEP_CSV}"                                    | tee -a run.log
for d in 0 32 64 96 112 128 144 160 192 224 256; do
    echo ""                                                                          | tee -a run.log
    echo "--- RESP_DELAY = ${d} cycles (rd=wr) ---"                                  | tee -a run.log
    python3 host/characterize.py \
        --port "$UART_PORT" \
        --channels "$SWEEP_CHANNELS" \
        --descriptors "$SWEEP_DESCRIPTORS" \
        --size "$SWEEP_SIZE" \
        --rd-delay "$d" --wr-delay "$d" \
        --output "$SWEEP_CSV" \
        -v >> run.log 2>&1 || true
done

echo ""                                                                              | tee -a run.log
echo "=== sweep CSV (${SWEEP_CSV}) ==="                                              | tee -a run.log
column -s, -t "$SWEEP_CSV" 2>/dev/null | tee -a run.log

echo ""                                                                              | tee -a run.log
echo "=== done — last 30 lines of run.log ==="                                       | tee -a run.log
tail -30 run.log
