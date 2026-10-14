#!/usr/bin/env bash
# ------------------------------------------------------------
# HIVE-C core generator — emits the VexRiscv netlist into vendor/vexriscv/
# ------------------------------------------------------------
# Usage:
#   ./generate_hive_cores.sh            # generate (cached clone reuse)
#   ./generate_hive_cores.sh --force    # re-clone and regenerate
#
# Pins the upstream VexRiscv rev and the in-repo Scala configuration
# (bin/vexriscv/HiveCGen.scala), clones VexRiscv into a scratch build
# dir, runs SpinalVerilog, and copies the emitted netlist into
# vendor/vexriscv/ with a provenance record. Requires: git, java,
# sbt on PATH (see vault handbook / owner machine setup).
# ------------------------------------------------------------
set -euo pipefail

# Pinned to VexRiscv master @ baf7dc8 (2026-10-13). The 1.0.1 tag pins
# sbt 0.13.16 + Scala 2.11.6, whose toolchain cannot run on this machine's
# Java 21 (sbt 0.13 installs a SecurityManager; Scala 2.11.6 predates modern
# JDKs). Master carries Scala 2.12.18 + SpinalHDL 1.13.0, which do. The
# sbt launcher version is forced to the machine's 1.10.7 below (master's
# build.properties says 1.6.0) and both facts are recorded in PROVENANCE.
VEXRISCV_REPO="https://github.com/SpinalHDL/VexRiscv"
VEXRISCV_REV="${VEXRISCV_REV:-baf7dc82f855eddaf5b0a20a6802c526f127e38a}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HIVE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"                 # hive-serv/
RDS_ROOT="$(cd "${HIVE_ROOT}/../../../.." && pwd)"          # repo root (4 up: compute-eng-ip, components, projects, root)
BUILD_DIR="${HIVE_CORES_BUILD:-${HIVE_ROOT}/.build/vexriscv}"
OUT_DIR="${RDS_ROOT}/vendor/vexriscv"
CONFIG_SRC="${SCRIPT_DIR}/vexriscv/HiveCGen.scala"

for tool in git java sbt; do
  command -v "$tool" >/dev/null 2>&1 || { echo "Error: '$tool' not on PATH" >&2; exit 1; }
done
[[ -f "${CONFIG_SRC}" ]] || { echo "Error: ${CONFIG_SRC} missing" >&2; exit 1; }

# --- clone (or reuse cache) -----------------------------------------------
if [[ "${1:-}" == "--force" ]]; then rm -rf "${BUILD_DIR}"; fi
if [[ ! -d "${BUILD_DIR}/.git" ]]; then
  echo ">> fetching VexRiscv @ ${VEXRISCV_REV}"
  mkdir -p "${BUILD_DIR}"
  git -C "${BUILD_DIR}" init --quiet
  git -C "${BUILD_DIR}" remote add origin "${VEXRISCV_REPO}"
  git -C "${BUILD_DIR}" fetch --quiet --depth 1 origin "${VEXRISCV_REV}"
  git -C "${BUILD_DIR}" checkout --quiet FETCH_HEAD
else
  echo ">> reusing cached clone at ${BUILD_DIR} (rm it or --force to refresh)"
fi
CLONE_COMMIT="$(git -C "${BUILD_DIR}" rev-parse HEAD)"

# Master pins sbt 1.6.0, which predates Java 21 support; force the launcher
# pinned on this machine. Build-def change only, recorded in PROVENANCE.
SBT_VERSION="$(sbt --script-version 2>/dev/null || echo 1.10.7)"
printf 'sbt.version=%s\n' "${SBT_VERSION}" > "${BUILD_DIR}/project/build.properties"

# --- install the hive config into the tree --------------------------------
cp "${CONFIG_SRC}" "${BUILD_DIR}/src/main/scala/vexriscv/demo/HiveCGen.scala"

# --- generate --------------------------------------------------------------
echo ">> sbt runMain vexriscv.demo.HiveCGen (first run downloads SpinalHDL)"
( cd "${BUILD_DIR}" && sbt --batch "runMain vexriscv.demo.HiveCGen" )

[[ -f "${BUILD_DIR}/VexRiscv.v" ]] || { echo "Error: VexRiscv.v was not emitted" >&2; exit 1; }

# --- publish ---------------------------------------------------------------
mkdir -p "${OUT_DIR}"
cp "${BUILD_DIR}/VexRiscv.v" "${OUT_DIR}/VexRiscv.v"
[[ -f "${BUILD_DIR}/hive_c.yaml" ]] && cp "${BUILD_DIR}/hive_c.yaml" "${OUT_DIR}/hive_c.yaml"
SHA="$(sha256sum "${OUT_DIR}/VexRiscv.v" | cut -d' ' -f1)"
cat > "${OUT_DIR}/PROVENANCE.md" <<EOF
# PROVENANCE — vendor/vexriscv

Generated netlist for the HIVE-C master controller core (RTL Design Sherpa
hive-serv component).

- **Upstream:** ${VEXRISCV_REPO}
- **Version:** ${VEXRISCV_REV} (clone commit ${CLONE_COMMIT})
- **Configuration:** \`projects/components/compute-eng-ip/hive-serv/bin/vexriscv/HiveCGen.scala\`
  (RV32IM, no compressed, no MMU, no caches, machine CSRs, reset 0x0000_0000)
- **Generated:** $(date -u +%Y-%m-%d) by \`hive-serv/bin/generate_hive_cores.sh\`
- **Toolchain note:** upstream \`project/build.properties\` (sbt 1.6.0) is
  overridden to sbt ${SBT_VERSION} for Java 21 compatibility; see the
  header comment in the generator script for why the 1.0.1 tag is not used.
- **Netlist sha256:** ${SHA}
- **License:** MIT (VexRiscv, SpinalHDL; see upstream COPYING at the tag above)

## Regenerate

\`\`\`bash
projects/components/compute-eng-ip/hive-serv/bin/generate_hive_cores.sh --force
\`\`\`

Requires java + sbt on PATH. The emitted Verilog is checked in so simulation,
lint, and CI do not need the Scala toolchain — regeneration is a deliberate,
reviewed act.
EOF
echo ">> vendor/vexriscv/ updated (sha256 ${SHA:0:16}...)"
