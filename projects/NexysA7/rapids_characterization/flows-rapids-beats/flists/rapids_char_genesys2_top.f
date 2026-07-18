# Filelist for rapids_char_genesys2_top — Genesys 2 (Kintex-7 XC7K325T-2) build.
# Location: projects/NexysA7/rapids_characterization/flows-rapids-beats/flists/rapids_char_genesys2_top.f
#
# Reuses the entire Nexys top filelist (harness + DUT + host front-end +
# board helpers + rapids_char_top itself) and adds only the Genesys 2 board
# wrapper, which turns the 200 MHz LVDS sysclk into 100 MHz via an MMCM and
# instantiates rapids_char_top unchanged. IBUFDS / MMCME2_BASE / BUFG are
# Xilinx unisim primitives supplied by Vivado (this is a Vivado-only target).

# ---- Everything the Nexys top needs (includes rapids_char_top.sv) ----
-f $REPO_ROOT/projects/NexysA7/rapids_characterization/flows-rapids-beats/flists/rapids_char_top.f

# ---- Genesys 2 board wrapper (MMCM + pin mapping) ----
$REPO_ROOT/projects/NexysA7/rapids_characterization/flows-rapids-beats/rtl/rapids_char_genesys2_top.sv
