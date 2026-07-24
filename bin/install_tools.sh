#!/usr/bin/env bash
# Install the RTL toolchain: Verilator, oss-cad-suite (yosys/sby/iverilog/
# gtkwave), sv2v, Verible.
#
#   bash bin/install_tools.sh              # everything
#   bash bin/install_tools.sh --no-formal  # skip oss-cad-suite (~2 GB)
#   bash bin/install_tools.sh --prefix DIR # install somewhere else
#
# Layout is deliberately identical to the workstation's, so `source env_python`
# works afterwards with no edits:
#
#   $PREFIX/verilator-5.020/bin/verilator   -> symlink to the apt binary
#   $PREFIX/oss-cad-suite/bin/*             yosys, sby, iverilog, gtkwave
#   $PREFIX/sv2v                            sv2v binary
#   $PREFIX/verible/bin/*                   verible-verilog-*
#
# THE VERILATOR TRAP, which this script exists to get right:
#
#   Verilator is PINNED at 5.020. Newer releases have cocotb VCD/FST generation
#   bugs that produce corrupt or empty waves rather than an error, so a silent
#   upgrade costs a debugging session before anyone suspects the simulator.
#   Ubuntu 24.04 ships exactly 5.020-1, so apt is the right source.
#
#   But oss-cad-suite BUNDLES Verilator 5.045, and env_python prepends the
#   oss-cad-suite bin directory to PATH. If apt's verilator is only at
#   /usr/bin, oss-cad-suite wins the PATH race and you silently simulate on
#   5.045 -- the exact thing the pin forbids.
#
#   env_python's last PATH line prepends $PREFIX/verilator-5.020/bin, which is
#   how the workstation wins that race. We reproduce it with a symlink dir, so
#   the pinned binary is last-prepended and therefore first-found.
set -euo pipefail

PREFIX="/mnt/data/tools"
WANT_VERILATOR="5.020"
SV2V_VER="v0.0.13"
VERIBLE_VER="v0.0-4017-g62aee204"
DO_FORMAL=1

while [ $# -gt 0 ]; do
    case "$1" in
        --prefix) PREFIX="$2"; shift 2 ;;
        --no-formal) DO_FORMAL=0; shift ;;
        -h|--help) sed -n '2,30p' "$0"; exit 0 ;;
        *) echo "unknown arg: $1" >&2; exit 2 ;;
    esac
done

say()  { printf '\n\033[1m== %s\033[0m\n' "$*"; }
ok()   { printf '\033[32mok\033[0m   %s\n' "$*"; }
warn() { printf '\033[33mWARN\033[0m %s\n' "$*"; }
die()  { printf '\033[31mFAIL\033[0m %s\n' "$*"; exit 1; }

need() { command -v "$1" >/dev/null 2>&1; }
for t in curl tar; do need $t || die "missing prerequisite: $t"; done

# Fall back to a writable location rather than failing late on a sandbox that
# does not expose /mnt/data.
if ! mkdir -p "$PREFIX" 2>/dev/null; then
    if sudo -n true 2>/dev/null && sudo mkdir -p "$PREFIX" 2>/dev/null; then
        sudo chown "$(id -u):$(id -g)" "$PREFIX"
    else
        PREFIX="$HOME/.rtlds-tools"
        warn "default prefix not writable; using $PREFIX"
        mkdir -p "$PREFIX"
    fi
fi
say "Installing into $PREFIX"

# ---------------------------------------------------------------- Verilator --
say "Verilator (pinned $WANT_VERILATOR)"
if ! need verilator; then
    if need apt-get; then
        # apt-get update exits non-zero if ANY configured source fails -- and a
        # sandbox often carries third-party PPAs (deadsnakes, ondrej/php, ...)
        # that the egress proxy 403s. Those are irrelevant to Verilator, which
        # lives in the main Ubuntu archive; the good sources still refresh, so a
        # partial-update failure must NOT abort us under `set -e`. The install
        # below is the real success gate.
        sudo apt-get update -qq \
            || warn "apt-get update had partial failures (unreachable third-party repos); continuing"
        sudo apt-get install -y -qq verilator build-essential ccache perl python3-venv \
            || die "apt-get install verilator failed (main Ubuntu archive unreachable?)"
    else
        die "no apt-get and no verilator; build $WANT_VERILATOR from source"
    fi
fi
HAVE="$(verilator --version | awk '{print $2}')"
if [ "$HAVE" = "$WANT_VERILATOR" ]; then
    ok "Verilator $HAVE (matches pin)"
else
    warn "Verilator $HAVE != pinned $WANT_VERILATOR"
    warn "Waves may be silently corrupt. Build $WANT_VERILATOR from source if tests misbehave."
fi

# The shim dir that wins the PATH race against oss-cad-suite's 5.045.
mkdir -p "$PREFIX/verilator-$WANT_VERILATOR/bin"
for b in verilator verilator_bin verilator_coverage; do
    src="$(command -v $b 2>/dev/null || true)"
    [ -n "$src" ] && ln -sf "$src" "$PREFIX/verilator-$WANT_VERILATOR/bin/$b"
done
ok "pinned-Verilator shim at $PREFIX/verilator-$WANT_VERILATOR/bin"

# ------------------------------------------------------------ oss-cad-suite --
if [ "$DO_FORMAL" = 1 ]; then
    say "oss-cad-suite (yosys, sby, iverilog, gtkwave)"
    FRESH_OSS=0   # did WE just install it (and therefore own its layout)?
    HAVE_OSS=0    # is a usable suite present at the end, ours or pre-existing?
    if [ -x "$PREFIX/oss-cad-suite/bin/yosys" ]; then
        HAVE_OSS=1
        ok "already present: $("$PREFIX/oss-cad-suite/bin/yosys" -V | head -1)"
    else
        # Resolve the newest release rather than pinning a date that rots.
        TAG="$(curl -fsSL https://api.github.com/repos/YosysHQ/oss-cad-suite-build/releases/latest \
               | grep -m1 '"tag_name"' | cut -d'"' -f4 || true)"
        # Formal is optional and this suite is ~2 GB, so a filtered-egress
        # sandbox (GitHub release downloads 403 behind the proxy, exactly as the
        # sv2v/Verible fetches below) must warn-and-skip, never abort the whole
        # toolchain -- simulation needs none of this.
        if [ -z "$TAG" ]; then
            warn "could not resolve oss-cad-suite release (proxy/no network?); skipping -- formal will not run"
        else
            STAMP="${TAG//-/}"
            URL="https://github.com/YosysHQ/oss-cad-suite-build/releases/download/$TAG/oss-cad-suite-linux-x64-$STAMP.tgz"
            echo "  downloading $TAG (~2 GB, this takes a while)..."
            if curl -fL --progress-bar "$URL" -o "$PREFIX/oss-cad-suite.tgz" \
               && tar -xzf "$PREFIX/oss-cad-suite.tgz" -C "$PREFIX"; then
                FRESH_OSS=1
                HAVE_OSS=1
                ok "installed $("$PREFIX/oss-cad-suite/bin/yosys" -V | head -1)"
            else
                warn "oss-cad-suite download/extract failed (proxy/no network?); skipping -- formal will not run"
            fi
            rm -f "$PREFIX/oss-cad-suite.tgz"
        fi
    fi
    # Belt and braces on a suite WE installed: do not leave a second verilator
    # to be found by anything that bypasses env_python's PATH ordering. Only
    # done on a fresh install - an oss-cad-suite that was already here belongs
    # to the user and is not ours to rearrange; the shim above already wins.
    if [ "$FRESH_OSS" = 1 ]; then
        for b in verilator verilator_bin verilator_bin_dbg; do
            [ -e "$PREFIX/oss-cad-suite/bin/$b" ] && \
                mv -f "$PREFIX/oss-cad-suite/bin/$b" "$PREFIX/oss-cad-suite/bin/$b.unused" || true
        done
        ok "neutralised the bundled Verilator 5.045 in the suite we installed"
    elif [ "$HAVE_OSS" = 1 ]; then
        warn "pre-existing oss-cad-suite left untouched; it bundles Verilator 5.045"
        warn "-> the $PREFIX/verilator-$WANT_VERILATOR/bin shim is what keeps the pin winning"
    fi
else
    warn "skipping oss-cad-suite (--no-formal): yosys/sby/sv2v-based formal will not run"
fi

# --------------------------------------------------------------------- sv2v --
# sv2v is formal-preprocessing tooling, so it follows --no-formal like the
# oss-cad-suite above. Its GitHub release download can also 403 behind an
# egress proxy; that must warn-and-skip, never abort -- simulation needs none
# of this. (The old `curl && unzip` chain left /tmp/sv2v-x absent on a failed
# fetch, and the following `find` then aborted the whole script under `set -e`.)
if [ "$DO_FORMAL" = 1 ]; then
    say "sv2v $SV2V_VER (formal preprocessing)"
    if [ -x "$PREFIX/sv2v" ]; then
        ok "already present: $("$PREFIX/sv2v" --version 2>&1 | head -1)"
    elif ! need unzip; then
        warn "unzip missing; skipped sv2v"
    elif curl -fsSL "https://github.com/zachjs/sv2v/releases/download/$SV2V_VER/sv2v-Linux.zip" -o /tmp/sv2v.zip 2>/dev/null; then
        unzip -qo /tmp/sv2v.zip -d /tmp/sv2v-x
        found="$(find /tmp/sv2v-x -name sv2v -type f | head -1)"
        [ -n "$found" ] && install -m755 "$found" "$PREFIX/sv2v" && ok "installed $("$PREFIX/sv2v" --version 2>&1 | head -1)"
        rm -rf /tmp/sv2v.zip /tmp/sv2v-x
    else
        warn "could not fetch sv2v $SV2V_VER; formal preprocessing unavailable (optional)"
    fi
else
    warn "skipping sv2v (--no-formal): formal preprocessing will not run"
fi

# ------------------------------------------------------------------ Verible --
say "Verible $VERIBLE_VER (style lint)"
if [ -x "$PREFIX/verible/bin/verible-verilog-lint" ]; then
    ok "already present"
else
    URL="https://github.com/chipsalliance/verible/releases/download/$VERIBLE_VER/verible-$VERIBLE_VER-linux-static-x86_64.tar.gz"
    if curl -fsSL "$URL" -o /tmp/verible.tgz 2>/dev/null; then
        mkdir -p "$PREFIX/verible" && tar -xzf /tmp/verible.tgz -C "$PREFIX/verible" --strip-components=1
        rm -f /tmp/verible.tgz
        ok "installed $("$PREFIX/verible/bin/verible-verilog-lint" --version 2>&1 | head -1)"
    else
        warn "could not fetch Verible $VERIBLE_VER; style lint unavailable (optional)"
    fi
fi

# -------------------------------------------------------------------- report --
say "Result"
export PATH="$PREFIX/oss-cad-suite/bin:$PATH"
export PATH="$PREFIX/verilator-$WANT_VERILATOR/bin:$PATH"
export PATH="$PREFIX:$PREFIX/verible/bin:$PATH"
for t in verilator yosys sby sv2v iverilog gtkwave verible-verilog-lint; do
    if need "$t"; then ok "$t -> $(command -v $t)"; else warn "$t not available"; fi
done
echo
echo "Verilator that will actually be used: $(verilator --version 2>/dev/null)"

if [ "$PREFIX" != "/mnt/data/tools" ]; then
    cat <<EOF

NOTE: env_python hardcodes /mnt/data/tools. Since tools went to $PREFIX,
export these after sourcing it (order matters - the pinned Verilator must be
prepended LAST so it beats oss-cad-suite):

  export PATH="$PREFIX/oss-cad-suite/bin:\$PATH"
  export PATH="$PREFIX:$PREFIX/verible/bin:\$PATH"
  export PATH="$PREFIX/verilator-$WANT_VERILATOR/bin:\$PATH"
EOF
fi
echo
echo "Next: source env_python"
