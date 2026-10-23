# Cocotb sim top for the LiteDRAM A/B harness: char_engine_harness (the same
# injectors / observers as the pumice and granite sim tops) driving LiteX's
# litedram_core_sim. The sim core is GENERATED and not tracked: regenerate it
# WITH the BIOS first (flows-litedram-uart/regen.sh --bios, or litedram_gen
# --sim without --no-compile-software) or init_done never asserts.
-f $REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2-characterization/flows-litedram-uart/rtl/filelists/litedram_char_harness.f
# the core's VexRiscv (standard variant), copied beside it from pythondata-cpu-vexriscv by the regen
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2-characterization/flows-litedram-uart/gen/sim/gateware/VexRiscv.v
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2-characterization/flows-litedram-uart/gen/sim/gateware/litedram_core_sim.v
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tb/litedram_char_uart_tb_top.sv
