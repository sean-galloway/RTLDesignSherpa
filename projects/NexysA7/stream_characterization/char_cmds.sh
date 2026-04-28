#!/bin/bash
# STREAM Characterization — multi-axis FPGA sweep driver
#
# Drives host/characterize.py through several 1-D and 2-D sweeps. Each
# experiment writes its rows into its own CSV so the data is ready to plot
# independently (no row tagging or post-filtering needed).
#
# characterize.py CLI (per-run):
#   --channels N        scalar — active channels for this run
#   --descriptors N     scalar — descriptors per channel
#   --size SIZE         per-descriptor transfer size: e.g. 4KB / 64KB / 1MB.
#                       total bytes = channels * descriptors * size.
#   --rd-delay N        read-response per-beat hold cycles  (CSR RESP_DELAY[15:0])
#   --wr-delay N        write-response per-beat hold cycles (CSR RESP_DELAY[31:16])
#                       0 = bypass on either channel.
#   --output FILE.csv   creates if missing, appends if present (single header).
#
# CSV columns:
#   name, num_channels, descriptors, total_bytes,
#   rd_delay_cyc, wr_delay_cyc,
#   cycles, seconds, throughput_MBps,
#   r2r_cycles, r2r_MBps,
#   w2w_cycles, w2w_MBps,
#   pass, timeout
#
# NOTE: assumes the bitstream/programming on the board already matches the
# checked-in RTL (RESP_DELAY @ 0x3C and the R2R/W2W cycle stamps @ 0x40-0x5C).
# If you've just `git pull`-ed or are running on a board that hasn't seen the
# latest harness, run `make bitstream && make program` once first.

set -e

rm -f run.log
touch run.log

UART_PORT=/dev/serial/by-id/usb-Digilent_Digilent_USB_Device_210292B7D46F-if01-port0

# Helper — one characterize.py invocation. Args: CSV CH DESC SIZE DELAY
run_one() {
    local CSV=$1; local CH=$2; local DESC=$3; local SIZE=$4; local D=$5
    python3 host/characterize.py \
        --port "$UART_PORT" \
        --channels "$CH" \
        --descriptors "$DESC" \
        --size "$SIZE" \
        --rd-delay "$D" --wr-delay "$D" \
        --output "$CSV" \
        -v >> run.log 2>&1 || true
}

# Track every CSV we write so the end-of-script summary prints them all.
SWEEP_CSVS=()

#==============================================================================
# Sweep 1 — Response-delay sweep (1-D)
#   1 channel, 1 descriptor, 512 KB total. Delay = 0..7.
#   Shows the per-beat response-delay -> bandwidth penalty in fine steps.
#==============================================================================
DELAY_CSV=delay_sweep_1desc_1ch_512KB.csv
SWEEP_CSVS+=("$DELAY_CSV")
rm -f "$DELAY_CSV"

echo "=== Sweep 1: delay 1desc 1ch 512KB (delay 0..7 step 1) ==="              | tee -a run.log
echo "    accumulating into ${DELAY_CSV}"                                       | tee -a run.log
for d in 0 1 2 3 4 5 6 7; do
    echo "--- RESP_DELAY = ${d} cycles (rd=wr) ---"                             | tee -a run.log
    run_one "$DELAY_CSV" 1 1 512KB "$d"
done

#==============================================================================
# Sweep 2 — Descriptor-count sweep (1-D)
#   1 channel, descriptors 1..16, 512 KB per descriptor, delay = 0.
#   Total bytes scales with N: 512KB ... 8MB. Shows whether descriptor
#   chaining hides startup/drain overhead — r2r/w2w should stay flat
#   while total_MBps climbs as overhead is amortized.
#==============================================================================
DESC_CSV=desc_sweep_1ch_512KB_delay0.csv
SWEEP_CSVS+=("$DESC_CSV")
rm -f "$DESC_CSV"

echo ""                                                                         | tee -a run.log
echo "=== Sweep 2: 1ch x Ndesc x 512KB (N=1..16, delay=0) ==="                  | tee -a run.log
echo "    accumulating into ${DESC_CSV}"                                        | tee -a run.log
for n in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; do
    echo "--- descriptors = ${n} ---"                                           | tee -a run.log
    run_one "$DESC_CSV" 1 "$n" 512KB 0
done

#==============================================================================
# Sweep 3 — Channel-count sweep (1-D)
#   N channels, 1 descriptor, 512 KB per descriptor, delay = 0.
#   FPGA build is 4-channel; sweep 1..4 to see arbitration efficiency.
#==============================================================================
CHAN_CSV=channel_sweep_1desc_512KB_delay0.csv
SWEEP_CSVS+=("$CHAN_CSV")
rm -f "$CHAN_CSV"

echo ""                                                                         | tee -a run.log
echo "=== Sweep 3: Nch x 1desc x 512KB (N=1..4, delay=0) ==="                   | tee -a run.log
echo "    accumulating into ${CHAN_CSV}"                                        | tee -a run.log
for c in 1 2 3 4; do
    echo "--- channels = ${c} ---"                                              | tee -a run.log
    run_one "$CHAN_CSV" "$c" 1 512KB 0
done

#==============================================================================
# Sweep 4 — Transfer-size sweep (1-D)
#   1 channel, 1 descriptor, size 8KB..1MB, delay = 0.
#   Shows the engine's startup-cost amortization curve. r2r/w2w should
#   flatten quickly; total_MBps should asymptote toward r2r/w2w as size grows.
#==============================================================================
SIZE_CSV=size_sweep_1desc_1ch_delay0.csv
SWEEP_CSVS+=("$SIZE_CSV")
rm -f "$SIZE_CSV"

echo ""                                                                         | tee -a run.log
echo "=== Sweep 4: 1ch x 1desc x size (size=8KB..1MB, delay=0) ==="             | tee -a run.log
echo "    accumulating into ${SIZE_CSV}"                                        | tee -a run.log
for s in 8KB 16KB 32KB 64KB 128KB 256KB 512KB 1MB; do
    echo "--- size = ${s} ---"                                                  | tee -a run.log
    run_one "$SIZE_CSV" 1 1 "$s" 0
done

#==============================================================================
# Sweep 5 — Channels × delay (2-D)
#   Sweep channels {1,2,4} crossed with delay {0,2,4,8} at 1desc/512KB.
#   Question: do extra channels help tolerate response latency by keeping
#   more transactions in flight? Expectation: at delay>0, total_MBps should
#   scale with channels until the engine's outstanding-AW limit saturates.
#==============================================================================
CH_X_DLY_CSV=channels_x_delay_1desc_512KB.csv
SWEEP_CSVS+=("$CH_X_DLY_CSV")
rm -f "$CH_X_DLY_CSV"

echo ""                                                                         | tee -a run.log
echo "=== Sweep 5: channels x delay (1desc, 512KB) ==="                         | tee -a run.log
echo "    channels in {1,2,4}; delay in {0,2,4,8}"                              | tee -a run.log
echo "    accumulating into ${CH_X_DLY_CSV}"                                    | tee -a run.log
for c in 1 2 4; do
    for d in 0 2 4 8; do
        echo "--- channels=${c}, delay=${d} ---"                                | tee -a run.log
        run_one "$CH_X_DLY_CSV" "$c" 1 512KB "$d"
    done
done

#==============================================================================
# Sweep 6 — Descriptors × delay (2-D)
#   Sweep descriptors {1,2,4,8,16} crossed with delay {0,2,4,8} at 1ch/512KB.
#   Question: does descriptor chaining hide response latency? Expectation:
#   long chains amortize startup cost regardless of delay, so the *gap*
#   between r2r/w2w and total should shrink with more descriptors at every
#   delay value.
#==============================================================================
DESC_X_DLY_CSV=desc_x_delay_1ch_512KB.csv
SWEEP_CSVS+=("$DESC_X_DLY_CSV")
rm -f "$DESC_X_DLY_CSV"

echo ""                                                                         | tee -a run.log
echo "=== Sweep 6: descriptors x delay (1ch, 512KB) ==="                        | tee -a run.log
echo "    descriptors in {1,2,4,8,16}; delay in {0,2,4,8}"                      | tee -a run.log
echo "    accumulating into ${DESC_X_DLY_CSV}"                                  | tee -a run.log
for n in 1 2 4 8 16; do
    for d in 0 2 4 8; do
        echo "--- descriptors=${n}, delay=${d} ---"                             | tee -a run.log
        run_one "$DESC_X_DLY_CSV" 1 "$n" 512KB "$d"
    done
done

#==============================================================================
# Sweep 7 — Channels × descriptors (2-D, no delay)
#   Sweep channels {1,2,4} crossed with descriptors {1,4,16} at 512KB/delay=0.
#   Maps the 2-D peak-throughput surface in the no-latency regime, useful as
#   the "ideal-system" reference plane that the delay sweeps stretch away from.
#==============================================================================
CH_X_DESC_CSV=channels_x_desc_512KB_delay0.csv
SWEEP_CSVS+=("$CH_X_DESC_CSV")
rm -f "$CH_X_DESC_CSV"

echo ""                                                                         | tee -a run.log
echo "=== Sweep 7: channels x descriptors (512KB, delay=0) ==="                 | tee -a run.log
echo "    channels in {1,2,4}; descriptors in {1,4,16}"                         | tee -a run.log
echo "    accumulating into ${CH_X_DESC_CSV}"                                   | tee -a run.log
for c in 1 2 4; do
    for n in 1 4 16; do
        echo "--- channels=${c}, descriptors=${n} ---"                          | tee -a run.log
        run_one "$CH_X_DESC_CSV" "$c" "$n" 512KB 0
    done
done

#==============================================================================
# End-of-run summary — print every CSV in run.log so you can read all the
# tables in one place when scrolling back through the log.
#==============================================================================
echo ""                                                                         | tee -a run.log
echo "=== ALL SWEEP RESULTS ==="                                                | tee -a run.log
for f in "${SWEEP_CSVS[@]}"; do
    echo ""                                                                     | tee -a run.log
    echo "--- $f ---"                                                           | tee -a run.log
    column -s, -t "$f" 2>/dev/null | tee -a run.log
done

echo ""                                                                         | tee -a run.log
echo "=== run.log end ==="                                                      | tee -a run.log
