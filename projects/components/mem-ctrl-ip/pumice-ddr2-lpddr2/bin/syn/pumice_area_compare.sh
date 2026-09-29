#!/usr/bin/env bash
# Synthesize pumice_top twice — as-configured and with every queue depth
# halved — and emit a per-FUB area CSV for each.
#
#   bin/syn/pumice_area_compare.sh [output_dir]
#
# Needs yosys with the `slang` plugin: yosys' native Verilog frontend
# cannot parse pumice's SystemVerilog (it rejects a multi-term `return`
# in a package function), so the real SV frontend is required.
#
# The "halved" build never edits the repo. Five files carry queue-depth
# parameter DEFAULTS that pumice_core does not override; they are copied
# to a scratch overlay, sed-edited there, and a rewritten filelist points
# at the copies. NUM_ENTRIES/N_SRAM_SLOTS are top-level parameters and
# are overridden with slang's -G instead.
#
# Skid buffers (SKID_DEPTH_*) are deliberately NOT halved: they are AXI
# handshake pipeline registers, not capacity queues, so halving a 2-deep
# skid changes handshake behaviour rather than buffering.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJ="$(cd "$HERE/../.." && pwd)"
: "${REPO_ROOT:=$(cd "$PROJ/../../../.." && pwd)}"
export REPO_ROOT
OUT="${1:-$PROJ/reports/area}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$OUT"

RTL="$PROJ/rtl"
TOP_F="$RTL/filelists/top/pumice_top.f"

echo "== flattening $TOP_F"
python3 "$REPO_ROOT/bin/flatten_filelist.py" --resolve-env --absolute-paths \
    "$TOP_F" -o "$WORK/full.f" >/dev/null

# ---- halved overlay -------------------------------------------------
OVL="$WORK/half_rtl"
mkdir -p "$OVL/macro" "$OVL/fub"
for f in macro/pumice_mem_cmd_scheduler.sv macro/pumice_dfi_layer.sv \
         fub/pumice_dfi_cdc.sv fub/pumice_wr_intake.sv \
         fub/pumice_rd_intake.sv; do
    cp "$RTL/$f" "$OVL/$f"
done

sed -i 's/parameter int CMD_FIFO_DEPTH = 8,/parameter int CMD_FIFO_DEPTH = 4,/' \
    "$OVL/macro/pumice_mem_cmd_scheduler.sv"
sed -i -e 's/parameter int CMD_FIFO_DEPTH = 8,/parameter int CMD_FIFO_DEPTH = 4,/' \
       -e 's/parameter int WD_FIFO_DEPTH  = 16,/parameter int WD_FIFO_DEPTH  = 8,/' \
       -e 's/parameter int RD_FIFO_DEPTH  = 16,/parameter int RD_FIFO_DEPTH  = 8,/' \
    "$OVL/macro/pumice_dfi_layer.sv"
sed -i 's/parameter int TOK_DEPTH    = 4,/parameter int TOK_DEPTH    = 2,/' \
    "$OVL/fub/pumice_dfi_cdc.sv"
sed -i -e 's/parameter int AW_FIFO_DEPTH     = 4,/parameter int AW_FIFO_DEPTH     = 2,/' \
       -e 's/parameter int WDATA_FIFO_DEPTH  = 16,/parameter int WDATA_FIFO_DEPTH  = 8,/' \
       -e 's/parameter int B_FIFO_DEPTH      = 4,/parameter int B_FIFO_DEPTH      = 2,/' \
    "$OVL/fub/pumice_wr_intake.sv"
sed -i -e 's/parameter int AR_FIFO_DEPTH     = 4,/parameter int AR_FIFO_DEPTH     = 2,/' \
       -e 's/parameter int ORDER_FIFO_DEPTH  = 8,/parameter int ORDER_FIFO_DEPTH  = 4,/' \
       -e 's/parameter int RD_FIFO_DEPTH     = 16,/parameter int RD_FIFO_DEPTH     = 8,/' \
    "$OVL/fub/pumice_rd_intake.sv"

# sed no-ops silently on a pattern miss, so prove every edit landed.
EXPECT=13
GOT=$(grep -hc "= *[0-9]*,$" /dev/null; grep -h "parameter int .*DEPTH" \
        "$OVL/macro/pumice_mem_cmd_scheduler.sv" "$OVL/macro/pumice_dfi_layer.sv" \
        "$OVL/fub/pumice_dfi_cdc.sv" "$OVL/fub/pumice_wr_intake.sv" \
        "$OVL/fub/pumice_rd_intake.sv" \
      | grep -v SKID | grep -cE "= *(2|4|8),") || true
if [ "$GOT" -ne "$EXPECT" ]; then
    echo "ERROR: expected $EXPECT halved depths in the overlay, found $GOT" >&2
    echo "       (a parameter default changed upstream — update the seds)" >&2
    exit 1
fi

sed -e "s|$RTL/macro/pumice_mem_cmd_scheduler.sv|$OVL/macro/pumice_mem_cmd_scheduler.sv|" \
    -e "s|$RTL/macro/pumice_dfi_layer.sv|$OVL/macro/pumice_dfi_layer.sv|" \
    -e "s|$RTL/fub/pumice_dfi_cdc.sv|$OVL/fub/pumice_dfi_cdc.sv|" \
    -e "s|$RTL/fub/pumice_wr_intake.sv|$OVL/fub/pumice_wr_intake.sv|" \
    -e "s|$RTL/fub/pumice_rd_intake.sv|$OVL/fub/pumice_rd_intake.sv|" \
    "$WORK/full.f" > "$WORK/half.f"

# ---- synthesis ------------------------------------------------------
# Two builds per variant: flattened (the realistic, fully optimized
# total) and hierarchy-preserved (needed to attribute area to a FUB;
# larger, because module boundaries block cross-boundary optimization).
run_yosys () {          # run_yosys <tag> <filelist> <flatten?> [-G ...]
    local tag="$1" flist="$2" flat="$3"; shift 3
    local incs srcs dir="$WORK/$tag"
    mkdir -p "$dir"
    incs=$(grep '^+incdir+' "$flist" | sed 's/^+incdir+/-I /' | tr '\n' ' ')
    srcs=$(grep -E '\.(sv|v)$' "$flist" | grep -v '^#' | tr '\n' ' ')
    local hier="" synth="synth -top pumice_top -flatten"
    if [ "$flat" = "hier" ]; then
        hier="--best-effort-hierarchy"
        synth="synth -top pumice_top"
    fi
    {
        echo "plugin -i slang"
        echo "read_slang $hier --top pumice_top $* $incs $srcs"
        echo "hierarchy -top pumice_top"
        echo "$synth"
        echo "abc -g simple"      # uniform generic library => comparable
        echo "opt_clean"
        echo "tee -o $dir/stat.txt stat"
    } > "$dir/synth.ys"
    # stdout -> stderr: this function's stdout IS its return value, and
    # the slang frontend prints its build summary on stdout.
    yosys -q -l "$dir/yosys.log" "$dir/synth.ys" >&2
    echo "$dir/stat.txt"
}

echo "== baseline"
BASE_FLAT=$(run_yosys base_flat "$WORK/full.f" flat)
BASE_HIER=$(run_yosys base_hier "$WORK/full.f" hier)
echo "== halved queues"
HALF_FLAT=$(run_yosys half_flat "$WORK/half.f" flat -G NUM_ENTRIES=4 -G N_SRAM_SLOTS=4)
HALF_HIER=$(run_yosys half_hier "$WORK/half.f" hier -G NUM_ENTRIES=4 -G N_SRAM_SLOTS=4)

python3 "$HERE/hier_csv.py" "$BASE_HIER" --flat-stat "$BASE_FLAT" \
    -o "$OUT/pumice_baseline_area.csv"
python3 "$HERE/hier_csv.py" "$HALF_HIER" --flat-stat "$HALF_FLAT" \
    -o "$OUT/pumice_half_area.csv"
echo "== wrote $OUT/pumice_{baseline,half}_area.csv"
