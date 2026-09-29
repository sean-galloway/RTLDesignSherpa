# Parameter sweep: carry-chain adder width (timing_characterization TASK-002).
# Only the FUB under test is enabled so each point compiles in under a minute
# and the per-FUB row in fub_slack.csv is the only interesting one; VIRTUAL_PINS
# because the port count changes with the parameter and I/O is not the question.
# Run:  cd fpga && make quartus-sweep QUARTUS_CFG=quartus/sweeps/carry_width.tcl QUARTUS_REPORTS_SUB=carry_width
set FREQS_MHZ    {150}
set SWEEP_PARAM  CARRY_WIDTH
set SWEEP_VALUES {8 16 32 64 128 256}
set PARAMETERS   {EN_NAND_TREE 0 EN_INVERTER_CHAIN 0 EN_XOR_TREE 0 EN_CARRY_CHAIN 0 EN_MULTIPLIER 0 EN_MUX_TREE 0 EN_QUEUE_DEPTH 0 EN_CLK_DIVIDER 0 EN_GRAY_COUNTER 0 EN_CARRY_CHAIN 1}
set VIRTUAL_PINS 1
set BUILD_DIR    fpga/build/quartus/carry_width
set REPORTS_DIR  fpga/reports/quartus/carry_width
