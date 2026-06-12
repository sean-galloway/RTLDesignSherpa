<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# 2.1 Use Cases

## UC-1: FPGA Technology Comparison

**Goal:** Compare combinational delay across FPGA families for technology selection.

**Flow:**
1. Synthesize `char_top` against Xilinx Artix-7, UltraScale+, and Intel Cyclone/Stratix
2. Extract per-FUB setup slack from timing reports
3. Compute delay-per-logic-level for each technology
4. Select technology based on critical path requirements

**Key FUBs:** All nine, with emphasis on carry_chain and multiplier_tree for datapath decisions.

## UC-2: Pipeline Depth Budgeting

**Goal:** Determine maximum combinational depth at a target frequency.

**Flow:**
1. Select target frequency (e.g., 500 MHz) and target FPGA
2. Sweep NAND_LEVELS and INVERTER_COUNT parameters
3. Find the parameter value where setup slack crosses zero
4. Use this as the pipeline depth budget for production datapaths

**Key FUBs:** nand_chain, inverter_chain, xor_tree.

## UC-3: Multiplier Implementation Selection

**Goal:** Decide whether to use DSP slices or LUT fabric for multipliers.

**Flow:**
1. Synthesize multiplier_tree with MULT_TYPE=0 (inferred, tool chooses DSP)
2. Synthesize again with MULT_TYPE=1..4 (structural, forces LUT fabric)
3. Compare Fmax and resource utilization
4. Determine crossover width where DSP becomes advantageous

**Key FUBs:** multiplier_tree with varying MULT_TYPE and MULT_WIDTH.

## UC-4: Memory Inference Threshold Discovery

**Goal:** Find FIFO depth where synthesis tool switches memory implementation.

**Flow:**
1. Sweep FIFO_DEPTH from 4 to 4096
2. Check utilization reports for LUTRAM, BRAM, URAM usage
3. Note transition boundaries
4. Use findings to guide FIFO sizing in production designs

**Key FUBs:** queue_depth.

## UC-5: Educational Demonstration

**Goal:** Teach synthesis optimization and timing analysis concepts.

**Flow:**
1. Show how LFSR and dont_touch attributes prevent optimization
2. Demonstrate parameter sweeps and timing report interpretation
3. Compare identical RTL across different targets
4. Illustrate the relationship between logic depth and maximum frequency
