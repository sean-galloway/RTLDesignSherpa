#!/usr/bin/env bash
#==============================================================================
# gen.sh — build the rapids_char_top bitstream (Nexys A7-100T)
#==============================================================================
# Thin wrapper around Vivado batch mode. Resolves REPO_ROOT from the git repo
# (unless already exported) and invokes the build TCL.
#
# Usage:
#   ./bin/gen.sh                 # full synth + impl + bitstream
#   ./bin/gen.sh project         # create the Vivado project only
#   ./bin/gen.sh program         # flash the board over JTAG
#   RAPIDS_NUM_CHANNELS=8 ./bin/gen.sh   # override built channel count
#
# Requires Vivado on PATH (override with the VIVADO env var).
#==============================================================================
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FLOW_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
TCL_DIR="${FLOW_ROOT}/tcl"

# Resolve REPO_ROOT: honor an existing export, else derive from git.
if [[ -z "${REPO_ROOT:-}" ]]; then
    REPO_ROOT="$(git -C "${FLOW_ROOT}" rev-parse --show-toplevel)"
fi
export REPO_ROOT

VIVADO="${VIVADO:-vivado}"
VIVADO_BATCH=("${VIVADO}" -mode batch -nojournal -notrace)

target="${1:-bitstream}"
case "${target}" in
    project)   tcl="${TCL_DIR}/create_project.tcl" ;;
    bitstream) tcl="${TCL_DIR}/build_all.tcl" ;;
    program)   tcl="${TCL_DIR}/program_fpga.tcl" ;;
    *)
        echo "Unknown target '${target}' (expected: project | bitstream | program)" >&2
        exit 2
        ;;
esac

echo "[gen] REPO_ROOT=${REPO_ROOT}"
echo "[gen] target=${target} -> ${tcl}"
echo "[gen] NUM_CHANNELS=${RAPIDS_NUM_CHANNELS:-4 (default)}"

# Run from the flow root so relative Vivado outputs (build/, reports/, .jou/.log)
# land under flows-rapids-beats/.
cd "${FLOW_ROOT}"
exec "${VIVADO_BATCH[@]}" -source "${tcl}"
