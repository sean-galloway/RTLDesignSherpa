#!/bin/bash
# Re-roll bitstream + program + run baseline DMA.
# Source me from this directory: `. cmds.sh`

set -e

rm -f run.log
touch run.log

echo "=== make clean + make bitstream (re-roll P&R) ==="            | tee -a run.log
make clean >> run.log 2>&1
make bitstream >> run.log 2>&1
echo "bitstream done"                                               | tee -a run.log

echo "=== post-route timing summary ==="                            | tee -a run.log
grep -A3 "WNS(ns)" reports/timing_summary.txt | head -5             | tee -a run.log

echo "=== make program ==="                                         | tee -a run.log
make program >> run.log 2>&1
echo "program done"                                                 | tee -a run.log

echo "=== baseline 1desc_1ch_512KB (largest known-good size) ==="   | tee -a run.log
python3 host/characterize.py --port /dev/serial/by-id/usb-Digilent_Digilent_USB_Device_210292B7D46F-if01-port0 --configs 1desc_1ch_512KB --size 512KB -v >> run.log 2>&1 || true

echo "=== done — last 30 lines of run.log ==="                      | tee -a run.log
tail -30 run.log
