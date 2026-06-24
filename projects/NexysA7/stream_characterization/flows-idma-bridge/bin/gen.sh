#!/bin/bash
# Generate iDMA RTL (rw_axi backend + desc64 SG frontend) and assemble per-top
# filelists for OOC area synthesis. Idempotent. Run after bin/setup.sh.
#
# Produces, under flows-idma-bridge/flists/:
#   deps.f            shared dependency sources (common_cells, axi, reg_if, ...)
#   incdirs.f         include directories
#   idma_backend.f    rw_axi backend closure   (top: idma_backend_synth_rw_axi)
#   idma_desc64.f     desc64 SG frontend closure (top: idma_desc64_synth)
#   axi_mux.f         AXI 8->1 mux closure       (top: axi_mux_synth_8)
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
IDMA="$HERE/external/iDMA"
BENDER="$HERE/bin/bender"
PY="${IDMA_PYTHON:-/mnt/data/github/RTLDesignSherpa/venv/bin/python}"
RT="$IDMA/.bender/git/checkouts/register_interface-b8f5b6eab31564be/vendor/lowrisc_opentitan/util/regtool.py"
mkdir -p "$HERE/flists"

echo "[gen] generating iDMA RTL (mario + regtool)"
cd "$IDMA"
make PYTHON="$PY" target/rtl/idma_backend_synth_rw_axi.sv >/dev/null 2>&1
make PYTHON="$PY" IDMA_REGTOOL="$RT" \
     target/rtl/idma_desc64_reg_pkg.sv target/rtl/idma_desc64_reg_top.sv >/dev/null 2>&1

echo "[gen] dependency filelist (bender)"
# Dependency sources only (the .bender checkouts), tb/sim excluded.
"$BENDER" script flist -t rtl -t synth 2>/dev/null \
  | grep '\.bender/git/checkouts/' \
  | grep -viE '/test/|/tb/|_tb\.sv|tb_|/sim/|tc_sram_impl|/deprecated/' \
  > "$HERE/flists/deps.f"

# Include dirs: every dep checkout's include/ plus iDMA's own.
( for d in "$IDMA"/.bender/git/checkouts/*/include; do echo "$d"; done
  echo "$IDMA/src/include"; echo "$IDMA/target/rtl/include" ) > "$HERE/flists/incdirs.f"

# --- iDMA rw_axi backend closure ---
cat > "$HERE/flists/idma_backend.f" <<EOF
$IDMA/src/idma_pkg.sv
$IDMA/src/backend/idma_error_handler.sv
$IDMA/src/backend/idma_axi_read.sv
$IDMA/src/backend/idma_axi_write.sv
$IDMA/src/backend/idma_channel_coupler.sv
$IDMA/src/backend/idma_dataflow_element.sv
$IDMA/src/backend/idma_legalizer_page_splitter.sv
$IDMA/target/rtl/idma_legalizer_rw_axi.sv
$IDMA/target/rtl/idma_transport_layer_rw_axi.sv
$IDMA/target/rtl/idma_backend_rw_axi.sv
$IDMA/target/rtl/idma_backend_synth_rw_axi.sv
EOF

# --- iDMA desc64 SG frontend closure ---
cat > "$HERE/flists/idma_desc64.f" <<EOF
$IDMA/src/idma_pkg.sv
$IDMA/target/rtl/idma_desc64_reg_pkg.sv
$IDMA/target/rtl/idma_desc64_reg_top.sv
$IDMA/src/frontend/desc64/idma_desc64_reg_wrapper.sv
$IDMA/src/frontend/desc64/idma_desc64_reshaper.sv
$IDMA/src/frontend/desc64/idma_desc64_reader.sv
$IDMA/src/frontend/desc64/idma_desc64_reader_gater.sv
$IDMA/src/frontend/desc64/idma_desc64_ar_gen.sv
$IDMA/src/frontend/desc64/idma_desc64_ar_gen_prefetch.sv
$IDMA/src/frontend/desc64/idma_desc64_top.sv
$IDMA/src/frontend/desc64/idma_desc64_synth_pkg.sv
$IDMA/src/frontend/desc64/idma_desc64_synth.sv
EOF

# --- AXI 8->1 mux (shared-memory-port arbiter, the 8-channel glue) ---
AXI_CK="$(echo "$IDMA"/.bender/git/checkouts/axi-*)"
cat > "$HERE/flists/axi_mux.f" <<EOF
$AXI_CK/src/axi_pkg.sv
$AXI_CK/src/axi_intf.sv
$AXI_CK/src/axi_mux.sv
EOF

echo "[gen] done. flists in $HERE/flists/"
