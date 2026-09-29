# Parameter sweep: NAND tree depth (timing_characterization TASK-002).
# Only the FUB under test is enabled so each point compiles in under a minute
# and the per-FUB row in fub_slack.csv is the only interesting one; VIRTUAL_PINS
# because the port count changes with the parameter and I/O is not the question.
# Run:  cd fpga && make quartus-sweep QUARTUS_CFG=quartus/sweeps/nand_levels.tcl QUARTUS_REPORTS_SUB=nand_levels
set FREQS_MHZ    {150}
set SWEEP_PARAM  NAND_LEVELS
set SWEEP_VALUES {4 6 8 10 12}
# NUM_FLOPS must be >= 2**NAND_LEVELS or char_top clamps the leaf count
# (NAND_ACTUAL_FLOPS) and the wrapped leaves fold: with the default 256 flops the
# 8/10/12-level points synthesized to the same 278 ALMs and 4 LUT levels on the
# first run. 4096 covers the deepest point here.
set PARAMETERS   {EN_NAND_TREE 0 EN_INVERTER_CHAIN 0 EN_XOR_TREE 0 EN_CARRY_CHAIN 0 EN_MULTIPLIER 0 EN_MUX_TREE 0 EN_QUEUE_DEPTH 0 EN_CLK_DIVIDER 0 EN_GRAY_COUNTER 0 EN_NAND_TREE 1 NUM_FLOPS 4096}
set VIRTUAL_PINS 1
set BUILD_DIR    fpga/build/quartus/nand_levels
set REPORTS_DIR  fpga/reports/quartus/nand_levels
