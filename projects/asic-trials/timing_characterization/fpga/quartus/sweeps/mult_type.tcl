# Parameter sweep: multiplier architecture (0 inferred/DSP, 1 dadda, 2 wallace, 3 wallace_csa, 4 dadda_4to2) (timing_characterization TASK-002).
# Only the FUB under test is enabled so each point compiles in under a minute
# and the per-FUB row in fub_slack.csv is the only interesting one; VIRTUAL_PINS
# because the port count changes with the parameter and I/O is not the question.
# Run:  cd fpga && make quartus-sweep QUARTUS_CFG=quartus/sweeps/mult_type.tcl QUARTUS_REPORTS_SUB=mult_type
set FREQS_MHZ    {150}
set SWEEP_PARAM  MULT_TYPE
set SWEEP_VALUES {0 1 2 3 4}
set PARAMETERS   {EN_NAND_TREE 0 EN_INVERTER_CHAIN 0 EN_XOR_TREE 0 EN_CARRY_CHAIN 0 EN_MULTIPLIER 0 EN_MUX_TREE 0 EN_QUEUE_DEPTH 0 EN_CLK_DIVIDER 0 EN_GRAY_COUNTER 0 EN_MULTIPLIER 1}
set VIRTUAL_PINS 1
set BUILD_DIR    fpga/build/quartus/mult_type
set REPORTS_DIR  fpga/reports/quartus/mult_type
