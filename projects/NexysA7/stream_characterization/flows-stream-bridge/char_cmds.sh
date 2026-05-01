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
#   --rd-delay N        read-response per-beat memory latency  (CSR RESP_DELAY[15:0])
#   --wr-delay N        write-response per-beat memory latency (CSR RESP_DELAY[31:16])
#                       Pipelined model: every beat dwells N cycles, but multiple
#                       beats are in flight in parallel up to the queue capacity.
#                       0 = 1-cycle minimum (FIFO register stage).
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

mkdir -p csv build
LOG=build/run.log
rm -f "$LOG"
touch "$LOG"

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
        -v >> "$LOG" 2>&1 || true
}

# Track every CSV we write so the end-of-script summary prints them all.
SWEEP_CSVS=()

#==============================================================================
# Sweep 1 — Response-delay sweep (1-D), maps the pipeline cliff
#   1 channel, 1 descriptor, 512 KB total. Delay 0..512.
#   With the pipelined memory-controller delay model, throughput stays flat
#   until the master's outstanding pipe (AR/AW_MAX_OUTSTANDING × burst_len ≈
#   128 beats with default cfg) stops covering the latency. Sweep spans well
#   past the predicted knee so we capture both the flat floor and the linear
#   degradation regime above it. Re-run after changing CFG_AR/AW_MAX_OUTSTANDING
#   in stream_char_cfg_pkg.sv to see the cliff shift.
#==============================================================================
DELAY_CSV=csv/delay_sweep_1desc_1ch_512KB.csv
SWEEP_CSVS+=("$DELAY_CSV")
rm -f "$DELAY_CSV"

echo "=== Sweep 1: delay 1desc 1ch 512KB (delay 0..512 — maps cliff) ==="      | tee -a "$LOG"
echo "    accumulating into ${DELAY_CSV}"                                       | tee -a "$LOG"
for d in 0 16 32 64 96 112 128 144 160 192 224 256 320 384 448 512; do
    echo "--- RESP_DELAY = ${d} cycles (rd=wr) ---"                             | tee -a "$LOG"
    run_one "$DELAY_CSV" 1 1 512KB "$d"
done

#==============================================================================
# Sweep 2 — Descriptor-count sweep (1-D)
#   1 channel, descriptors 1..16, 512 KB per descriptor, delay = 0.
#   Total bytes scales with N: 512KB ... 8MB. Shows whether descriptor
#   chaining hides startup/drain overhead — r2r/w2w should stay flat
#   while total_MBps climbs as overhead is amortized.
#==============================================================================
DESC_CSV=csv/desc_sweep_1ch_512KB_delay0.csv
SWEEP_CSVS+=("$DESC_CSV")
rm -f "$DESC_CSV"

echo ""                                                                         | tee -a "$LOG"
echo "=== Sweep 2: 1ch x Ndesc x 512KB (N=1..16, delay=0) ==="                  | tee -a "$LOG"
echo "    accumulating into ${DESC_CSV}"                                        | tee -a "$LOG"
for n in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16; do
    echo "--- descriptors = ${n} ---"                                           | tee -a "$LOG"
    run_one "$DESC_CSV" 1 "$n" 512KB 0
done

#==============================================================================
# Sweep 3 — Channel-count sweep (1-D)
#   N channels, 1 descriptor, 512 KB per descriptor, delay = 0.
#   FPGA build is 4-channel; sweep 1..4 to see arbitration efficiency.
#==============================================================================
CHAN_CSV=csv/channel_sweep_1desc_512KB_delay0.csv
SWEEP_CSVS+=("$CHAN_CSV")
rm -f "$CHAN_CSV"

echo ""                                                                         | tee -a "$LOG"
echo "=== Sweep 3: Nch x 1desc x 512KB (N=1..4, delay=0) ==="                   | tee -a "$LOG"
echo "    accumulating into ${CHAN_CSV}"                                        | tee -a "$LOG"
for c in 1 2 3 4; do
    echo "--- channels = ${c} ---"                                              | tee -a "$LOG"
    run_one "$CHAN_CSV" "$c" 1 512KB 0
done

#==============================================================================
# Sweep 4 — Transfer-size sweep (1-D)
#   1 channel, 1 descriptor, size 8KB..1MB, delay = 0.
#   Shows the engine's startup-cost amortization curve. r2r/w2w should
#   flatten quickly; total_MBps should asymptote toward r2r/w2w as size grows.
#==============================================================================
SIZE_CSV=csv/size_sweep_1desc_1ch_delay0.csv
SWEEP_CSVS+=("$SIZE_CSV")
rm -f "$SIZE_CSV"

echo ""                                                                         | tee -a "$LOG"
echo "=== Sweep 4: 1ch x 1desc x size (size=8KB..1MB, delay=0) ==="             | tee -a "$LOG"
echo "    accumulating into ${SIZE_CSV}"                                        | tee -a "$LOG"
for s in 8KB 16KB 32KB 64KB 128KB 256KB 512KB 1MB; do
    echo "--- size = ${s} ---"                                                  | tee -a "$LOG"
    run_one "$SIZE_CSV" 1 1 "$s" 0
done

#==============================================================================
# Sweep 5 — Channels × delay (2-D)
#   Channels {1..4} crossed with delay {0..512} at 1desc/512KB.
#   With the pipelined model, the read/write engines are shared across all
#   channels (single AR/AW outstanding queue per engine), so cliff position
#   is set by the engine config, not the channel count. What channels DO
#   change is arbitration efficiency at low delay and how quickly bandwidth
#   degrades in the post-cliff regime (more channels share the same in-flight
#   budget). Expect cliff at the same L for every channel count; flat-region
#   throughput should rise with channel count (better arbitration overlap),
#   post-cliff slope should steepen.
#==============================================================================
CH_X_DLY_CSV=csv/channels_x_delay_1desc_512KB.csv
SWEEP_CSVS+=("$CH_X_DLY_CSV")
rm -f "$CH_X_DLY_CSV"

echo ""                                                                         | tee -a "$LOG"
echo "=== Sweep 5: channels x delay (1desc, 512KB) ==="                         | tee -a "$LOG"
echo "    channels in {1,2,3,4}; delay in {0,32,64,96,128,160,192,256,384,512}" | tee -a "$LOG"
echo "    accumulating into ${CH_X_DLY_CSV}"                                    | tee -a "$LOG"
for c in 1 2 3 4; do
    for d in 0 32 64 96 128 160 192 256 384 512; do
        echo "--- channels=${c}, delay=${d} ---"                                | tee -a "$LOG"
        run_one "$CH_X_DLY_CSV" "$c" 1 512KB "$d"
    done
done

#==============================================================================
# Sweep 6 — Descriptors × delay (2-D)
#   Descriptors {1,2,4,8,16} crossed with delay {0..512} at 1ch/512KB.
#   With the pipelined model, the engines maintain their outstanding queue
#   across descriptors as long as bursts are back-to-back, so the once-per-
#   transfer pipe-fill cost (L cycles) is paid once per chain — not per
#   descriptor. Long chains should amortize that fixed cost over more total
#   beats, narrowing the gap between r2r/w2w and total throughput at every
#   delay value. Cliff position itself shouldn't move with descriptor count.
#==============================================================================
DESC_X_DLY_CSV=csv/desc_x_delay_1ch_512KB.csv
SWEEP_CSVS+=("$DESC_X_DLY_CSV")
rm -f "$DESC_X_DLY_CSV"

echo ""                                                                         | tee -a "$LOG"
echo "=== Sweep 6: descriptors x delay (1ch, 512KB) ==="                        | tee -a "$LOG"
echo "    descriptors in {1,2,4,8,16}; delay in {0,32,64,96,128,160,192,256,384,512}" | tee -a "$LOG"
echo "    accumulating into ${DESC_X_DLY_CSV}"                                  | tee -a "$LOG"
for n in 1 2 4 8 16; do
    for d in 0 32 64 96 128 160 192 256 384 512; do
        echo "--- descriptors=${n}, delay=${d} ---"                             | tee -a "$LOG"
        run_one "$DESC_X_DLY_CSV" 1 "$n" 512KB "$d"
    done
done

#==============================================================================
# Sweep 7 — Channels × descriptors (2-D, no delay)
#   Sweep channels {1,2,4} crossed with descriptors {1,4,16} at 512KB/delay=0.
#   Maps the 2-D peak-throughput surface in the no-latency regime, useful as
#   the "ideal-system" reference plane that the delay sweeps stretch away from.
#==============================================================================
CH_X_DESC_CSV=csv/channels_x_desc_512KB_delay0.csv
SWEEP_CSVS+=("$CH_X_DESC_CSV")
rm -f "$CH_X_DESC_CSV"

echo ""                                                                         | tee -a "$LOG"
echo "=== Sweep 7: channels x descriptors (512KB, delay=0) ==="                 | tee -a "$LOG"
echo "    channels in {1,2,4}; descriptors in {1,4,16}"                         | tee -a "$LOG"
echo "    accumulating into ${CH_X_DESC_CSV}"                                   | tee -a "$LOG"
for c in 1 2 4; do
    for n in 1 4 16; do
        echo "--- channels=${c}, descriptors=${n} ---"                          | tee -a "$LOG"
        run_one "$CH_X_DESC_CSV" "$c" "$n" 512KB 0
    done
done

#==============================================================================
# End-of-run summary — print every CSV in run.log so you can read all the
# tables in one place when scrolling back through the log.
#==============================================================================
echo ""                                                                         | tee -a "$LOG"
echo "=== ALL SWEEP RESULTS ==="                                                | tee -a "$LOG"
for f in "${SWEEP_CSVS[@]}"; do
    echo ""                                                                     | tee -a "$LOG"
    echo "--- $f ---"                                                           | tee -a "$LOG"
    column -s, -t "$f" 2>/dev/null | tee -a "$LOG"
done

echo ""                                                                         | tee -a "$LOG"
echo "=== run.log end ==="                                                      | tee -a "$LOG"
