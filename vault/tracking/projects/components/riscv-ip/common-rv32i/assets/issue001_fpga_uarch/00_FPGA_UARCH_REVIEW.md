# riscv-ip FPGA microarchitecture review (2026-11-18)

Requested by the owner after the cache-ip and mem-ctrl-ip reviews: check the
RISC-V cores for structures shaped for an ASIC rather than an FPGA. Tracked as
riscv-ip/common-rv32i ISSUE-001.

## Scope and method

RTL exists for four of the eight riscv-ip directories: `common-rv32i` (decode,
immediate generator, ALU, package), `kestrel-rv32i` (single-cycle), `merlin-rv32i`
(5-stage pipeline) and `gatling-rv32i` (4-context barrel). peregrine, gyrfalcon
and garuda are structure only, about 3,800 lines of RTL in total.

Every number below is from Vivado 2025.1, part xc7a100tcsg324-1 (Nexys A7), with
a 10 ns clock. Each block was synthesized out of context (OOC), then
`opt_design`, `place_design`, `phys_opt_design` and `route_design`, and read with
`report_utilization -hierarchical` and `report_timing_summary`. Hierarchy
attribution comes from a second synthesis with `-flatten_hierarchy none`.

Caveats on reading the numbers:

- **OOC means no board around the block.** A core's memory ports are top-level
  ports, so the block RAM read latency and the board's I/O are not on the path.
  kestrel meets 100 MHz OOC but runs at 75 MHz on the board, where its worst
  path (~11.6 ns, board README) runs through the memories.
- **RVFI ports are outputs OOC, so their logic is kept.** On the board the tops
  leave `rvfi_order`, `rvfi_insn`, `rvfi_pc_*`, `rvfi_rs*` and `rvfi_mem_*`
  unconnected and Vivado trims that logic. See row 5.
- **One placement seed per build.** A worst slack within about 0.2 ns of zero
  moves between runs. Read the LUT and flop counts as the firm numbers and a
  slack change of under ~0.3 ns as noise.

## Headline

The large things are already FPGA-shaped, unlike cache-ip and mem-ctrl-ip:

- The register files are distributed RAM (kestrel, merlin: 48 LUTRAM) or
  duplicated block RAM with a registered read (gatling: 2 RAMB18).
- The program and data memories are registered-read block RAM (kestrel 4 RAMB36,
  gatling 16).
- There are no CAMs and no arrays dissolved into flops.

The findings are smaller and concentrated in two places. The **shared ALU** is
374 LUT in every core, the largest single block in each, and an equivalent
FPGA-shaped ALU is 205 to 306 LUT smaller. **merlin's pipeline registers**
reset and flush their whole payload, which makes 811 of its 814 flops
async-reset (FDCE) and costs about 212 LUT and the 100 MHz timing.

## Measured baseline

| Block | LUT | FF | of which FDCE | BRAM | WNS @ 10 ns | Worst path |
|---|---|---|---|---|---|---|
| kestrel_core | 1,149 | 100 | 97 | LUTRAM regfile | +0.388 | regfile read -> ALU -> regfile write, 12 levels |
| merlin_core | 1,583 | 814 | 811 | LUTRAM regfile | **-0.141** (11 endpoints) | MEM/WB `alu_y` -> forward -> branch / next PC -> ID/EX CE, 12 levels |
| gatling_core | 1,538 | 897 | 409 | 2 RAMB18 | +0.464 | regfile BRAM -> ALU / next PC -> halt -> `pc_q` CE, 11 levels |
| kestrel_mem_bram | 399 | 471 | 186 | 4 RAMB36 | +3.734 | |
| gatling_mem_bram | 661 | 788 | 495 | 16 RAMB36 | +2.982 | |

Per-module attribution (`-flatten_hierarchy none`, synthesis):

| Core | top-level logic | rv32i_alu | regfile | pipeline registers |
|---|---|---|---|---|
| kestrel | 549 LUT, 97 FF | **374** | 48 LUTRAM | (none) |
| merlin | 737 LUT, 101 FF | **374** | 48 LUTRAM | if_id 35, id_ex 91, ex_mem 120, mem_wb 2 LUT; 710 FF |
| gatling | 937 LUT, 890 FF | **374** | 50 LUT, 2 RAMB18 | (in top) |

## Findings

| # | Where | What | Measured / estimated effect | Contract change? |
|---|---|---|---|---|
| 1 | `common-rv32i/rtl/fub/rv32i_alu.sv` | three barrel shifters (`<<`, `>>`, `>>>`) and a second 33-bit compare for SLT/SLTU beside the add/sub | **measured:** kestrel -306 LUT (-27%), gatling -231 (-15%), merlin -205 (-13%); kestrel WNS +0.388 -> +1.233 | none: same ports, same result (checked, below) |
| 2 | `merlin-rv32i/rtl/fub/merlin_{if_id,id_ex,ex_mem,mem_wb}.sv` | the whole payload struct is async-reset and cleared on flush; only the valid and control bits need either | **measured:** FDCE 811 -> 130, -212 LUT, WNS -0.141 -> +0.133 | needs merlin regression + riscv-formal (below) |
| 3 | `merlin-rv32i/rtl/top/merlin_core.sv` | the critical path starts with the forwarding compare (`rd_addr == rs`), then the forwarded operand, branch compare and target, redirect, and the flush / stall that fans out to every pipeline register; `imem_addr_next` is driven from the same cone into the instruction RAM's address | 11 to 15 levels in every merlin variant; not measured | (a) none; (b) one more branch-penalty cycle |
| 4 | `gatling-rv32i/rtl/top/gatling_core.sv` | per-context `pc_q` (4 x 32), `cause_q`, `halted_q` in async-reset flops, written by a per-context loop and read twice through a `sel_q` mux (`imem_addr`, `d_pc`) | estimated: 128 FF and most of the read / write mux to ~11 LUTRAM; not measured | none if a per-context "held" bit stands in for the reset value |
| 5 | gatling `order_q`, kestrel `retire_count`, merlin `insn` / `rs1_rdata` / `rs2_rdata` / `imm` in EX/MEM and MEM/WB | state that exists only for RVFI | gatling: 256 FDCE + four 64-bit incrementers; merlin: ~256 FF of carried RVFI fields. Trimmed on the board (ports unconnected) | recorded no-action: costs only where RVFI is consumed |
| 6 | `kestrel_mem_bram`, `gatling_mem_bram` | the AXI-Lite write slave's W-channel `gaxi_skid_buffer`: 154 / 310 LUT for 78 FF | shared `rtl/amba` IP, outside riscv-ip; the same 2 to 4 LUT per flop seen in the mem-ctrl review | not riscv-ip's to change; both memory systems close with 3 to 3.7 ns of slack |
| 7 | kestrel on the board | 75 MHz, worst path ~11.6 ns through the memories; single-cycle by design | row 1 gives +0.85 ns OOC; whether it lifts the board clock needs a board build | none |

### 1. The ALU: one adder, one shifter

`rv32i_alu.sv` ORs eight result rows. Three of them are separate 32-bit barrel
shifters, and SLT/SLTU uses its own 33-bit signed compare
(`rv32i_alu.sv:62-63`) beside the add/sub adder (`rv32i_alu.sv:60`). On an FPGA a
32-bit barrel shifter is about 80 to 100 LUT, so three of them are most of the
374.

The variant keeps the ports and the OR-of-rows result, and changes two things:

- **One 33-bit adder for ADD, SUB, SLT and SLTU.** The operands are extended
  with the sign bit for SLT and a zero for SLTU, and the result of SLT/SLTU is
  bit 32 of the extended difference. That is one carry chain instead of two.
- **One right shifter for SRL, SRA and SLL.** The fill bit is `a[31]` for SRA and
  zero otherwise. SLL bit-reverses the operand on the way in and the result on
  the way out, which costs wires and no logic.

```systemverilog
assign is_slt = (op == SLT) || (op == SLTU);
assign is_sub = (op == SUB) || is_slt;
assign sgn    = (op == SLT);
assign ea  = {sgn & a[31], a};
assign eb  = {sgn & b[31], b};
assign sum = ea + (eb ^ {33{is_sub}}) + {32'd0, is_sub};   // lt = sum[32]

assign left   = (op == SLL);
assign sh_in  = left ? a_rev : a;                           // a_rev = bit-reversed a
assign sh_out = 32'($signed({(op == SRA) & a[31], sh_in}) >>> b[4:0]);
// SLL result = bit-reversed sh_out
```

**Equivalence check:** a Verilator testbench drove the original and the variant
side by side. Each of the 10 ops got 64 edge pairs (0, 1, all-ones, 0x80000000,
0x7FFFFFFF, 0x1F, 0x20, 0xAAAA5555), every shift amount 0 to 31 on two patterns,
and 200,000 random pairs. Result: 2,001,280 vectors, **0 mismatches**. Mutation
check: turning off the SRA sign fill in the variant gives 96,990 mismatches, so
the checker does fail when the variant is wrong.

| Core | LUT before | LUT after | WNS before | WNS after |
|---|---|---|---|---|
| kestrel | 1,149 | 843 | +0.388 | +1.233 |
| gatling | 1,538 | 1,307 | +0.464 | +0.204 |
| merlin | 1,583 | 1,378 | -0.141 | +0.227 |

gatling's slack moved down by 0.26 ns while staying met. Its worst path does not
run through the shifters (row 4's halt-to-PC cone), so this is the placement
noise described above, not a regression in the ALU path.

The ALU's `eq`, `lt` and `ltu` outputs are unconnected in all three cores, and
Vivado trims them. They are kept in the variant so the port list is unchanged.

### 2. merlin's pipeline registers: reset and flush the control, not the payload

Each of the four registers is:

```systemverilog
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) q_o <= '0;
    else if (flush)           q_o <= '0;
    else if (!stall)          q_o <= d_i;)
```

On a 7-series slice the async reset takes the flop's CLR pin, so the
synchronous flush has to go through a LUT in front of every payload bit,
including data that no one reads once `valid` is low. The variant splits each
register:

- The payload is a plain enable flop: `if (!stall) q_data <= d_i`.
- Only the fields that cause a side effect reset and flush: `valid`, `rd_wen`,
  `dmem_req`, `dmem_we`, `branch`, `jump`, `jalr`, `ls_misalign`, `halt_cause` and
  `csr_stub`, each where its struct has it.

Result: FDCE 811 -> 130, LUT 1,583 -> 1,371, WNS -0.141 -> +0.133 (11 failing
endpoints -> 0).

**Not regression-checked.** The variant is only correct if nothing reads a
payload field of a flushed or invalid stage without qualifying it. Forwarding
qualifies on `rd_wen`, which still flushes. RVFI fields are don't-care while
`rvfi_valid` is low. Two things would settle it: the merlin suite run with
`clean-all`, and riscv-formal's checks.

Combining rows 1 and 2 gave 1,240 LUT with WNS -0.229 on this seed. The path
moved into row 3's cone and is now 15 levels. Rows 1 and 2 remove logic; row 3
is what limits merlin's clock after they land.

**Checked 2026-11-19, on top of row 1 (committed 98eedce98).** Landed the
same day together with row 3a in merlin-rv32i TASK-003, which has the final
numbers. On its own it cost merlin its 100 MHz margin (below).

- The first run failed 45 of 54 tests and 35 of 42 riscv-formal checks. One
  payload read was unqualified: the core zeroes x0 during reset by writing the
  WB data with the address forced to 0, and the zero-data select read
  `mem_wb_q.rd_addr` (now payload, so stale) instead of the forced
  `wb_rd_addr`. Fixed in the patch.
- The load-use interlock `idex_is_load` was the one control consumer not
  gated by `valid`. A flushed IF/ID keeps its old instruction, and ID decodes
  it into ID/EX controls under `valid = 0`, so the interlock would stall one
  spurious cycle. The patch gates it with `id_ex_q.valid`, so cycle behaviour
  is unchanged.
- `test_merlin_pipe_regs.py` asserted that a flush zeroes every datapath field.
  It now asserts the new contract: the control fields clear and, under
  stall + flush, the payload holds.
- Gates with the fix: merlin suite 54/54 (`clean-all`, `run-all-full`),
  riscv-formal 42/42. The formal run is the stronger check, because the
  unreset payload starts unconstrained there, and it caught the x0 bug.

Routed from the tree, rows 1 + 2:

| merlin | LUT | FDCE | WNS |
|---|---|---|---|
| row 1 only (committed) | 1,378 | 811 | +0.227 |
| rows 1 + 2 | 1,268 | 130 | -0.408 |

The worst path is `u_id_ex/r_payload_reg[rs1_addr]` -> the forward select ->
branch resolution -> the ID/EX control flops, 12 levels with 73% route. That
is row 3's cone. Both builds of rows 1 + 2 (-0.229 on 11-18, -0.408 here)
miss timing, and both builds of row 1 alone meet it. So row 2 waited for
row 3a. With both (TASK-003), merlin is 1,262 LUT, FDCE 134, and meets
10 ns under three placer directives (+0.065 to +0.241). Row 1 alone fails
two of the same three (-0.216 to +0.227).

### 3. merlin's critical path: forwarding into branch resolution

In every merlin build the worst path has the same shape:

- **Baseline:** `u_mem_wb/q_o_reg[alu_y]` -> the forward mux -> the branch
  compare and target -> `imem_addr_next` -> the ID/EX clock enable.
- **Variant:** `u_ex_mem/q_data_reg[rd_addr]` -> the forward select -> the same
  cone -> the `halt_cause` flop.

Two standard FPGA moves, neither measured:

- **(a) Register the forwarding selects one stage early.** Compute in ID whether
  the instruction's rs1/rs2 match the rd of the instructions now in EX and MEM,
  and register that as one-hot select bits into ID/EX. This removes the 5-bit
  compares from the start of the path. Behaviour is unchanged.
- **(b) Register the redirect.** Resolve the branch in EX as now, but apply the
  redirect and flush from a flop in the next cycle. This takes the fan-out out of
  the cone, at the cost of one more branch-penalty cycle. That trade is itself a
  lesson for this rung.

`imem_addr_next` comes out of the same cone combinationally into the instruction
RAM's address. On the board that path ends at a block RAM address pin, which has
a larger setup time than a flop, so the board margin will be below the OOC
margin.

**Addendum (2026-11-21, merlin-rv32i TASK-004): (b) not taken; a
load-to-branch interlock instead.** After (a) the worst path started at
load data in WB. (b) would cost every taken branch a third bubble and
change PRD M2. The interlock costs only a branch or JALR that uses a
load one or two instructions ahead:
- The branch compare and the JALR target get their own operand select,
  the ALU's with load data removed from the MEM/WB arm.
- A branch or JALR in ID whose source is that load waits one cycle.
- Routed, three placer directives, base 8e14d4198 (merlin unchanged since):

| merlin_core | LUT | WNS Default / ExtraNetDelay_high / SpreadLogic_high |
|---|---|---|
| before | 1,262 | +0.131 / +0.241 / +0.065 |
| after | 1,320-1,334 | +0.356 / +0.231 / +0.284 |

- The worst case moves from +0.065 to +0.231, inside the 0.2 ns budget on
  all three. The worst path is now WB or EX/MEM `alu_y` -> the ALU
  operand -> `alu_y` -> the branch target -> the PC; a pc + imm target
  adder would take the ALU out of it, if more margin is wanted.
- Cost on the rv32ui battery's spike streams: 255 stalls in 225,324
  instructions (0.11 percent), 90 at distance 1 and 165 at distance 2,
  most in the load and store tests. That battery is not a workload; on C
  code the `lw; beqz` pattern will be more common.

### 4. gatling's per-context state

`pc_q`, `cause_q` and `halted_q` are `[NUM_HARTS-1:0]` vectors of async-reset
flops (`gatling_core.sv:164-166`). They are written by a loop over every
context (`gatling_core.sv:412-437`) and read through `sel_q` twice
(`gatling_core.sv:186` and `:200`).

Each context is touched once per rotation, so the FPGA shape is a 4-entry
distributed RAM read at the F context and written at the X context. The reset
and `hart_run` hold need a per-context "held" bit, which reads as `RESET_ADDR`
while set, because LUTRAM has no reset. That bit is 4 flops instead of 128 plus
the mux.

Not built or measured. The current worst path, regfile BRAM -> ALU / next PC ->
halt decision -> `pc_q` clock enable, would end at the LUTRAM write instead.

**Addendum (2026-11-19, gatling-rv32i TASK-004): built and measured as
described.**
- The held bit is `pc_fresh`. A halt leaves it alone, so a context that
  halts on its first instruction still reads that instruction's address,
  as the flops did.
- `cause_q` and `halted_q` stay flops. The `halted` and `halt_cause` ports
  present every context at once.
- Routed, three placer directives, base 8e14d4198:

| gatling_core | LUT (LUTRAM) | FF (FDCE) | WNS Default / ExtraNetDelay_high / SpreadLogic_high |
|---|---|---|---|
| before | 1,308 (0) | 894 (409) | +0.190 / +0.470 / +0.196 |
| after | 1,200 (22) | 772 (281) | +0.424 / +0.506 / +0.660 |

- The LUTRAM count is 22, not 11: Vivado builds the 4 x 32 RAM as 34 RAMD32
  and 10 RAMS32.
- The worst path ends where predicted, at the RAM write enable or a
  `cause_q` enable.

### 5. RVFI-only state

| Core | State that exists only for RVFI |
|---|---|
| gatling | `order_q`: 4 x 64-bit counters (256 FDCE plus four 64-bit incrementers); W-stage `w_insn`, `w_pc`, `w_pc_wdata`, `w_rs1`, `w_rs2`, `w_mem_*` |
| kestrel | `retire_count` (64-bit) |
| merlin | `insn`, `rs1_rdata`, `rs2_rdata` and `imm` carried through EX/MEM and MEM/WB (about 256 flops) |

The board tops leave those RVFI ports unconnected, so Vivado trims all of it on
the board, and the OOC numbers above overstate the board by that amount. It
costs only where RVFI is consumed (riscv-formal, the spike-lockstep sims), which
is its purpose. Recorded as no action.

### 6 and 7

- **Row 6** is shared AMBA IP and is recorded here only so the memory-system
  numbers are not misread.
- **Row 7** is kestrel's deliberate single-cycle design. Row 1's +0.85 ns is the
  only change here likely to move the board clock, and a board build would say
  whether it does.

**Addendum (2026-11-21): row 7 measured; the board moves to 80 MHz.** With
row 1 in, the board build is about 400 LUT smaller (1,613 against 2,026
before the rework's last step) and its worst path is block RAM -> the
port-A fetch address. Two findings set the clock:
- A met board build does not measure margin. Vivado stops improving once
  the period is met: 81.8 MHz gave +0.118 under the build's placer
  directive and +0.007 / +0.012 / +0.118 under three more, and 80 MHz gave
  +0.048 and +0.013 / +0.028 / +0.048 -- the slack hugs zero whatever the
  period.
- The fix is to make the tool carry the 0.2 ns budget: setup uncertainty
  0.2 ns on the harness clock in the board XDC, restored after the
  placement-time over-constraint, so routing works against the period
  less the budget. 80 MHz then meets at +0.012 / +0.009 / +0.000 / +0.012
  (four directives), +0.2 ns real margin on every one.

| Board clock | WNS (build's directive) | Board | Throughput |
|---|---|---|---|
| 75 MHz (2026-10-20, before row 1) | +0.156 | 42/42 | 72.2 MIPS |
| 83.3 MHz | +0.009 | 42/42 | 80.2 MIPS |
| 81.8 MHz | +0.118 (worst directive +0.007) | 42/42 | 78.7 MIPS |
| **80 MHz, 0.2 ns budget in the XDC** | **+0.012 with the budget, +0.212 real** | **42/42, CPI 1.039** | **77.0 MIPS** |

## Suggested order

1. **Row 1, adopt the ALU.** It is contract-free and equivalence-checked, it
   saves 205 to 306 LUT in every core, and common-rv32i owns it. After it lands,
   run the kestrel, merlin and gatling suites (`clean-all` first) and the
   riscv-formal runs.
2. **Row 2, merlin's registers,** with the merlin regression and riscv-formal as
   the gate.
3. **Row 3 (a), merlin's forwarding selects,** measured the same way. Row 3 (b)
   is a design choice for the owner: one more branch-penalty cycle buys clock.
   (Not taken, 2026-11-21: a load-to-branch interlock instead, merlin-rv32i
   TASK-004.)
4. **Row 4, gatling's PC file,** measured.
5. **Row 7,** a kestrel board build after row 1, to see whether 75 MHz moves.

## Reproducing

```tcl
# vivado -mode batch -source ooc.tcl -tclargs <top> <filelist> <clkport> <outdir>
# env: REPO_ROOT, RV32I_COMMON_ROOT, KESTREL_ROOT, MERLIN_ROOT, GATLING_ROOT,
#      CONVERTERS_ROOT; optional AB_DIR swaps in same-named files from a variant dir
lassign $argv top fl clkport out
source "$::env(REPO_ROOT)/make/tcl/filelist_utils.tcl"
lassign [filelist::flatten $fl] srcs incdirs defines
foreach s $srcs { read_verilog -sv $s }
set_part xc7a100tcsg324-1
synth_design -top $top -mode out_of_context -flatten_hierarchy rebuilt -include_dirs $incdirs
create_clock -period 10.000 -name clk [get_ports $clkport]
opt_design; place_design; phys_opt_design; route_design
report_utilization -hierarchical -hierarchical_depth 4 -file $out/util_hier_impl.txt
report_timing_summary -max_paths 10 -file $out/timing_impl.txt
```

Tops and filelists: `kestrel_core` and `kestrel_mem_bram` from `kestrel_all.f`,
`merlin_core` from `merlin_all.f`, `gatling_core` and `gatling_mem_bram` from
`gatling_all.f`. The clock port is `clk` on the cores and `aclk` on the memory
systems.
