# FPGA microarchitecture review: AXI front end + DFI/CDC back end (pumice/granite common-ip)

Read-only review. Nothing in the repo was modified. All paths below are under `/mnt/data/github/RTLDesignSherpa/`; "common-ip" means `projects/components/mem-ctrl-ip/common-ip/rtl/`.

## 0. Board configuration as actually built (granite, 2026-10-29, 100 MHz, DDR-400)

Read from `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite/rtl/granite_char_top.sv:215-236` and `projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_core.sv:109-122`:

| Parameter | Value | Consequence |
|---|---|---|
| Host AXI data | 64 | `granite_char_top.sv:217` |
| DRAM_BEAT_WIDTH / device | 32 / x16, DRAM_BL=4, DFI_RATE=2 | BL_SHIFT=1, BL_PUMICE=2, **BURST_WORDS=1**, DFI word = 64 b (`granite_core.sv:113-117`). One AXI beat == one DRAM burst, so every "per-burst" structure degenerates to one beat per slot. |
| AXI_ID_WIDTH | 8 | `granite_char_macro.sv:27` |
| RD_RET_DEPTH | **64**, not 32 | Harness/macro default is 32 (`granite_char_harness.sv:55`) but `granite_char_top.sv:332-335` overrides to 64 unless `GRANITE_RD_RET_DEPTH` is defined, and `fpga/tcl/create_project.tcl:248-254` only ever defines `PUMICE_RD_RET_DEPTH`, which the granite top does not read. The memory note "RD_RET_DEPTH=32" is the harness default, not the board netlist. |
| INTAKE_FIFO_DEPTH / AXI_SKID_DEPTH | 0 / 2 | `granite_char_macro.sv:50-51` |
| DFI_CMD/WD/RD_FIFO_DEPTH | 4 / 16 / 4 | `granite_char_macro.sv:62-64` |
| **DFI_CDC_EN** | **0** | `granite_char_macro.sv:47`; `.dfi_clk(mc_clk)` at `granite_char_macro.sv:435-438`. The board build has NO async crossing: `mc_dfi_cdc` elaborates its `g_sync` branch (sync FIFOs). The 241-LUT figure is the synchronous form. pumice's `build-perf` harness also ties `mc_clk(aclk)` (`ddr2_char_harness.sv:134,748`). |
| SHARED_ADDR_MAP | 0 | two address mappers (`granite_char_macro.sv:52`) |
| HAS_SNARF / AR_STAGE_REG / MERGE_MARK_REG / RET_BYPASS / RET_FALLTHRU / CMD_FALLTHRU | 0 / 1 / 1 / 1 / 1 / 1 | `granite_pkg.sv:64-90`. BYPASS/FALLTHRU/CMD_FALLTHRU were committed 10-31 (ff8c64d18, 4f0603044), i.e. AFTER the 10-29 build; they are not in the measured numbers. |
| NARROW_EN | 1 (default, `macro/mc_axi4_plane.sv:69`) | `mc_axi4_narrow_pack` committed 11-03 (79788fd8e), also NOT in the 10-29 numbers. NARROW_DEPTH = RD_RET_DEPTH+8 = 72 (`mc_axi4_plane.sv:72`). |

Measured (`.../granite/fpga/reports_sys100_2026-10-29_ddr400/utilization_hier.txt:150-166`): mc_axi4_plane 1097 LUT / 1176 FF / 1 RAMB36; rd_intake 193 (slave_rd 101, order_fifo 75); **rd_ring 506 LUT / 629 FF, of which ring body 373 / 613 and u_issue_q 133 LUT (125 logic) / 16 FF**; wr_intake 258 (slave_wr 185); wr_split 76; rd_split 66; dfi_plane 284 (cdc 241 of which 118 LUTRAM: wd_fifo 67, cmd_fifo 104 (80 logic), rd_fifo 58). Chip: 36,691 LUT, 33,719 FF, 2,106 LUTRAM, 2 RAMB36 (`utilization_impl.txt:35-42,106`). WNS 0.021 ns at 100 MHz, met (`timing_summary.txt:154-158`).

## 1. Reset style (asked explicitly)

`rtl/amba/includes/reset_defs.svh:55-56,64`: `ALWAYS_FF_RST` expands unconditionally to `always_ff @(posedge clk or negedge rst)`. The header (lines 21-36) says the sync option was removed 2026-09-06. So every `ALWAYS_FF_RST` block in the mem-ctrl tree is **asynchronous reset**, and the chip flop table confirms it: 22,790 CE+async-reset, 690 CE+async-set, 10,058 CE+sync-reset, 181 CE+sync-set, zero flops without reset (`utilization_impl.txt:53-64`). The 10k sync flops are the PeakRDL CSR/harness; the controller is essentially all async.

Where this costs on 7-series in this slice:
- `gaxi_skid_buffer.sv:129-131`: every data slot bit is async-reset AND explicitly zeroed when vacated (lines 147, 161). 6,430 flops of skid data chip-wide (49 instances, sum from `utilization_hier.txt`) carry a reset they do not need.
- `gaxi_fifo_sync.sv:210-216` / `gaxi_fifo_async.sv:356-362`: the REGISTERED=1 output register is async-reset, so when a FIFO does go to BRAM the output flop cannot be absorbed into the RAMB output register (DOA_REG), costing a LUT-side register stage and the BRAM clock-to-out. REGISTERED=0 (the default everywhere in this slice) avoids that but forbids BRAM entirely (see 3.6).
- `mc_rd_return_ring.sv:269-274`: `r_src[i] <= TW'(i)` on reset gives 384 flops distinct async set/reset values (these are a large share of the 690 async-SET flops), and makes the table un-RAM-able. The reset value is dead: every allocation rewrites `r_src[r_tail]` (line 297) before the slot is used.
- Good: the data arrays that must be RAM are already reset-free and unconditionally clocked: ring `r_mem` (`mc_rd_return_ring.sv:359-362`, `(* ram_style = "block" *)` at 198), FIFO `mem` (`gaxi_fifo_sync.sv:204-208`, `gaxi_fifo_async.sv:350-354`). These infer LUTRAM/BRAM correctly; the hierarchy report shows the FIFO memories as LUTRAM with 0 FF (e.g. `u_rd_fifo` 44 LUTRAM / 8 FF). The "32x64 FIFO becomes 2048 flops" failure does NOT happen here for `gaxi_fifo_*`; it does happen for `gaxi_skid_buffer`, by design.

## 2. Summary table (ranked by expected LUT saving, then timing risk)

| # | Structure | file:line | Size at board config | Measured / est. LUT, FF | Why ASIC-shaped | FPGA alternative | Gives up |
|---|---|---|---|---|---|---|---|
| 1 | `gaxi_skid_buffer` shift-register skid (shared primitive) | `rtl/amba/gaxi/gaxi_skid_buffer.sv:82,128-170,204` | DEPTH=2 x 70-76 b per AXI channel; 49 instances chip-wide | **6,366 LUT / 6,430 FF chip-wide** (17% of LUTs); ~286 LUT in the two intakes (`slave_rd` 101, `slave_wr` 185) | Every slot bit is a 4-way mux (new data / shift from slot+1 / clear-to-zero / hold) selected by a 4-bit count compare, with async reset and explicit zeroing of the vacated tail. ~1 LUT per flop measured. | Canonical two-register skid: output reg + one skid reg, `out.D = skid_vld ? skid_q : in_d`, no shifting, no data reset, `ready = !skid_vld` registered. ~0.5 LUT per flop. | Nothing functional at DEPTH=2; DEPTH 3-8 would need a separate small FIFO form. Est. saving **~3k LUT chip-wide, ~140 in this slice**. |
| 2 | Return-ring shadow/source tracking (read combiner) | `common-ip/fub/mc_rd_return_ring.sv:130-131,147-151,284-285,294-310,320` | 64 x (1 shadow + 6 src) = 448 FF; two 64-entry 6-bit equality sweeps | Ring body went **106 -> 373 LUT, 229 -> 613 FF** between 10-17 and 10-29; the only ring commit in that window is bea5b861f (10-28, TASK-060), which added exactly this. Est. ~250 LUT for the two sweeps + per-slot write selects. | Two full-depth CAM-style compare sweeps every cycle (`r_src[i]==r_tail` for alloc_ready, `r_src[i]==w_iq_rd_ticket` for shadow-ready), plus a 64-entry table with 2 variable-index write ports (alloc at 297, mark at 303-304). | (a) Delete sweep 2 exactly: evaluate shadow readiness at fetch, `w_fptr_ready = r_focc!=0 && (r_shadow[r_fptr] ? r_ready[r_src[r_fptr]] : r_ready[r_fptr])`; `r_src[r_fptr]` is already read (line 248). Sound because the source is pinned until the shadow fetches, so `r_ready[src]` cannot be cleared by re-allocation (clear only at 295 on `r_tail`, which the pin blocks). (b) Sweep 1 (tail pinned): pipeline one cycle (tail moves at most 1/cycle, compute for `r_tail+1`) to take it off the alloc_ready path; or make it a per-slot 2-bit pin count with the CAM refusing a merge into a saturated source (needs a `src_pinnable` handshake from the store, outside this slice). (c) Drop the `TW'(i)` reset on `r_src` (dead value). | (a) nothing. (b) count form bounds shadows per source. Est. **~150-250 LUT, 0-384 async-set pins**. |
| 3 | Return ring itself (RD_RET_DEPTH=64, 1 beat/slot) | `mc_rd_return_ring.sv:198-199,359-362,186-187,250-251` | `r_mem` 64 x 64 b in 1 RAMB36 (4 Kb of 36 Kb); ticket FIFO 64 x 6 | 1 RAMB36 (fine) + `u_issue_q` 133 LUT (125 logic) for a 64x6 FIFO | The ring IS already the FPGA-native shape (BRAM + ticket FIFO + small valid vector, header lines 24-30): random-access write by ticket, in-order read by fetch pointer, registered BRAM read, 2-deep prefetch skid. Not a CAM. The costs that are not native are #2 above and the index arithmetic `ticket*AXI_BEATS_PER_BURST + beat` (186-187, 250-251), which is a plain concatenation at BURST_WORDS=1 but written as a 32-bit multiply-add. | Keep. Write the indices as `{ticket, beat}` (BCW bits) so the tool never sees a multiply. Note the `u_issue_q` 125 logic LUTs cannot be a 64x6 FIFO alone (its memory is 8 LUTRAM); Vivado has re-attributed ring logic into it, so treat ring+issue_q = 506 as one number. | Nothing. |
| 4 | `mc_axi4_narrow_pack` (not yet in a board build) | `common-ip/fub/mc_axi4_narrow_pack.sv:175,207-222,258-268,277-292,303-319,372-387` | AWQ 8 x 70 b LUTRAM; wrec 72 x 7, rrec 72 x 15 (non-pow2, 128-entry LUTRAM); 64 b accumulator + 8 b strobe acc; byte-merge mux 64 b | est. **250-350 LUT / ~90 FF** when NARROW_EN=1 (default) | Byte-lane merge is a 64-bit mux (258-261) plus the whole AW/AR/W/R path passing COMBINATIONALLY through the block: `m_awvalid` depends on `fub_awvalid && fub_awready` in the same cycle (195-204), `fub_wready` depends on `fub_awvalid` (250-252, 267-268), `word_len()` does a 9-bit variable shift and add in the AR/AW path (158-165). | On the board no narrow traffic exists (char engines are full width) — set `NARROW_EN=0` for the board netlist and keep it for pumice/granite proper. If kept: register the AW/AR rewrite (one cycle, both channels), and move the W pack into the write store's beat SRAM via byte-write-enables (7-series RAMB has per-byte WE; LUTRAM does not, so this only helps if the store is BRAM-backed, which `mc_wr_data_cam`/fifo store is outside this slice). | One AW/AR cycle of latency if registered. |
| 5 | Two `mc_addr_mapper` barrel shifters on a live CSR | `common-ip/fub/mc_addr_mapper.sv:96-120`; instantiated `fub/mc_rd_intake.sv:268-287`, `fub/mc_wr_intake.sv:342-361` | 32-bit word shifted right by `w_blsb` (0..10), masked, re-shifted left; x2 | est. **50-100 LUT each** (the hier report attributes only 17 own LUTs to rd_intake, below what the shifter needs, so attribution is unreliable here) | Runtime-variable field extraction with 32-bit shifters for a knob (`hwif_out.ADDR_MAP.bank_lsb`, `granite_top_geared.sv:523`) that changes only at init. | Precompute per-bit select masks once when the CSR is written (a registered decode of 11 cases), or on the board make `bank_lsb` a compile-time constant like FIXED_TIMINGS (`granite_core.sv:95-104` precedent). SHARED_ADDR_MAP=1 was measured -23% BW (`granite_char_macro.sv:52`) so halving by sharing is already ruled out. | A CSR write latency of a few cycles before the new map is live; or runtime remap on the board. |
| 6 | `gaxi_fifo_sync` full/empty from NEXT pointers | `rtl/amba/gaxi/gaxi_fifo_sync.sv:122-125`; `rtl/common/fifo_control.sv:41-50,84-87` | all 8 sync FIFOs in the slice | small LUT; **timing**: the chip's worst path (0.021 ns) ends at `u_rd_ring/u_issue_q/fifo_control_inst/rd_empty_reg/D` from a TIMINGS CSR flop (`timing_worst.txt:15-22`) | `wr_ptr_bin_next` includes the current handshake, so the producer's whole valid cone (scheduler pick, timers) lands on the flag flop D. The FIFO is not a pipeline cut for its producer. | Derive full/empty from registered pointers (+1 cycle of pessimism, which at depth 64 is free), or carry an explicit occupancy counter. | 1 cycle of visible latency through the ticket FIFO (the return beat waits a cycle longer at most). |
| 7 | `mc_dfi_cdc` async branch (pumice / DFI_CDC_EN=1 builds only) | `common-ip/fub/mc_dfi_cdc.sv:125-269`; `rtl/cdc/gaxi_fifo_async.sv:157-207,234-246,345-368` | cmd 4 x ~34, wd 16 x 73, wtok 16 x 1, rd (RD_RET_DEPTH*BURST_WORDS = 64) x 67, 2 token FIFOs of 4 x 1 | 10-17 async build: cdc 352 LUT / 162 LUTRAM / 210 FF | Gray-pointer FIFOs with LUTRAM data and combinational gray2bin on the synced pointer every cycle; correct and FPGA-reasonable. Five independent pointer crossings. | Keep the structure. If the rd FIFO must be 64 x 67 across the crossing, a FIFO36E1/xpm_fifo_async in one RAMB36 removes ~90 LUTRAM + ~40 logic. Collapse wd + wtok into ONE FIFO carrying `last` in the payload (see smell 5.1). | One BRAM. |
| 8 | DFI command path / formatter per phase | `common-ip/fub/mc_dfi_cmd_path.sv:252-320,399-417`; `fub/mc_xddr2_cmd_formatter.sv:361-390,395-415` | N_SUBCMD=1 at DFI 1:2; DFI_RATE=2 so the variable part-select (382-388) is a 2-way placement | dfi_plane minus cdc = **43 LUT** | Generic N-way merge of full-width per-sub buses, variable part-select by `w_cmd_phase`. | Keep. At N_SUBCMD=1 / DFI_RATE=2 it is already trivial and registered. | — |

No per-AXI-ID table exists in this slice: ID travels as FIFO payload only (`mc_rd_intake.sv:479-480,560-562`; `mc_wr_intake.sv:294-295,446-447`). `wr_done_id_i` originates in the storage plane, outside this review.

## 3. Detail per structure

### 3.1 gaxi_skid_buffer (chip-wide lever, 2 instances per intake)
- What: `r_data[SLOTS]` (`gaxi_skid_buffer.sv:82`), per-slot generate with `unique case ({wr_xfer, rd_xfer})` (128-170). Write position is `r_data_count == gi` (137), pop shifts every slot down (144-148), simultaneous push/pop writes slot `count-1` and shifts the rest (155-162). Output is `r_data[0]` (204), ready/valid registered (188-201).
- Access pattern: 1 write + 1 read per cycle but every slot's D sees three sources plus hold. For DEPTH=2, DW=76: 152 FF + ~150 LUT; the hierarchy shows ~1 LUT per FF across all 49 instances (6,366 / 6,430).
- Why ASIC-shaped: a shift-register FIFO is cheap in standard cells (mux + flop) and avoids a read pointer; on 7-series every bit costs a LUT6 for the 4-way select, and the "clear vacated tail" (147, 161) and async reset on data are pure overhead.
- Alternative: the two-register pipeline skid (output reg + skid reg). The output register's D is the only mux (skid_q vs in). Data flops take no reset. Expected ~0.5 LUT/FF.
- Give up: nothing at DEPTH=2. Board skids are all DEPTH=2 (`granite_char_macro.sv:51`, `axi4_slave_rd.sv:20`, `axi4_slave_wr.sv:22`); the converters/harness use the same primitive.

### 3.2 mc_rd_return_ring shadow/src (the doubling)
- Where: state 126-131; pinned sweep 147-151 feeding `alloc_ready_o` (152) -> `rt_alloc_ready_o` -> the CAM insert; shadow-ready sweep inside the return-fill (284-285); marking writes 294-310; shadow release at fetch 320.
- Dimensions: DEPTH=64, TW=6: `r_shadow` 64 FF, `r_src` 384 FF, `r_ready` 64 FF. `r_resp` (129, 282, 316) is 128 FF of dead logic: the only producer is `mc_dfi_rd_aligner.sv:173` `rd_resp_o = RESP_OKAY`, so Vivado prunes it (613 FF measured ~= 64+64+384 + 2x64 skid data + pointers). It is worth deleting in RTL so the skid's resp lanes and the drain mux also go.
- Access: two writes per cycle into `r_src`/`r_shadow` (alloc at `r_tail`, mark at `r_mk_ticket`) plus a write at `r_fptr` (320) and two full sweeps -> flops only.
- Alternative: in the table (#2). The key observation that makes (a) exact: a source slot's `r_ready` is set once at its own return (281) and only cleared at re-allocation (295), which the pin prevents until all shadows have fetched. So readiness of a shadow can be read at fetch time instead of being broadcast at return time.
- Also note `MERGE_MARK_REG` (302-310) was added for 100 MHz closure (comment 49-54): the mark write a cycle later creates the second write port that keeps the table out of LUTRAM.

### 3.3 Ring body: keep, with two cosmetic fixes
- `r_mem` is reset-free, `ram_style="block"`, 1-cycle registered read (`mc_rd_return_ring.sv:198-199,359-362`): correct BRAM idiom; 1 RAMB36 measured.
- Index arithmetic as 32-bit multiply-add (186-187, 250-251) is a concatenation at any power-of-two `AXI_BEATS_PER_BURST`; write it as such.
- The 2-deep prefetch skid `r_sk_*` (205-211, 330-344) is 128 FF + mux: fine.
- Same-cycle RAW: a fetch of slot s needs `r_ready[s]`, set the cycle after the last write (281), so BRAM write-then-read are never in the same cycle on the same address; the RET_BYPASS path (240-244) is explicitly exclusive with fetch. No hazard found.

### 3.4 Intake FIFOs and the AR stage
- Order FIFO 72 x 19 (`mc_axi4_plane.sv:514`, `mc_rd_intake.sv:494-504`): non-power-of-two depth is legal in `gaxi_fifo_sync` (`counter_bin` wraps at MAX) but a 72-entry LUTRAM is a 128-entry RAM128X1S per bit (2 LUT6/bit). 64 entries would halve it; the "+8" is for snarf hits that never enter the ring, and granite has HAS_SNARF=0.
- Side FIFOs of 2 bits x 6 (`mc_rd_intake.sv:453`, `mc_wr_intake.sv:262`) and the AW-meta 47 x 4 / B 10 x 4 (`mc_wr_intake.sv:297,449`): small LUTRAM, fine.
- AR stage register `r_s_*` (`mc_rd_intake.sv:337-344,393-417`) with AR_STAGE_REG=1 is the right FPGA move (cuts the mapper off the push path).
- `r_fwd <= w_head_len` 8-bit compares (546-547): tiny.

### 3.5 Splitter / chopper
- `mc_axi_burst_chopper.sv:132-163`: the first sub-command is driven combinationally from `fub_*` and continuation subs from the latched copy; `r_addr + AXI_BURST_BYTES` is a 32-bit adder (183). 66-76 LUT each, registered state, no loop. Keep. The comb pass-through of the first sub means host AW/AR -> (narrow pack) -> chopper -> skid.D is one combinational chain; with NARROW_EN=1 add `word_len()` to it.
- `mc_wr_splitter.sv:144-186`: 9-bit counters, zero-strobe padding; keep.

### 3.6 FIFO primitives
- `gaxi_fifo_sync.sv:27-30`: `MEM_STYLE` (FIFO_AUTO/SRL/BRAM) and `REGISTERED` (0 = `rd_data = mem[r_rd_addr]` combinational, line 219; 1 = async-reset output flop, 210-216). All instances in this slice use the defaults (AUTO, REGISTERED=0) -> asynchronous-read memory -> Vivado can only use LUTRAM. For the depths here (4-72 x 2-73 bits) that is the right answer and the report confirms LUTRAM with 0 FF. For anything 64+ deep and 64+ wide (the pumice async rd FIFO 64 x 67) BRAM would want REGISTERED=1 and a reset-free output register.
- `fifo_control.sv:66-82`: REGISTERED only delays the write pointer seen by the read side; it does not change where the data register lives.
- `gaxi_fifo_async.sv:82-84` enforces power-of-two depth for Gray; pointers via `counter_bingray` (157-178), 2-flop sync `glitch_free_n_dff_arn` (189-207), comb `gray2bin` (234-246), data array as in sync (345-368). `glitch_free_n_dff_arn.sv:339-350` carries NO `ASYNC_REG` attribute (only mentioned in a comment at 232-240), so Vivado will not keep the two synchronizer flops in one slice and the CDC report cannot classify the crossing as safe.

### 3.7 DFI plane
- `mc_dfi_cdc.sv` sync branch (271-367) is what the board builds: three sync FIFOs + a 1-bit token FIFO + sticky levels. 241 LUT of which 118 LUTRAM. The `u_cmd_fifo` row (104 LUT, 80 logic) for a 4 x 34 FIFO is again attribution noise from the formatter decode.
- `mc_dfi_cmd_path.sv` + `mc_xddr2_cmd_formatter.sv`: per-sub formatters merged by AND/OR (399-417); registered outputs (formatter 395-415); registered fire strobes (486-496). At N_SUBCMD=1 one formatter. Keep.
- `mc_dfi_wr_serializer.sv:75-99`: 32-bit `r_age` delay line indexed by `t_phy_wrlat_i` (a 32:1 one-bit mux), 3-bit owed counter; `dfi_wrdata_o = wd_data_i` straight from the FIFO read mux (112). Keep.
- `mc_dfi_rd_aligner.sv:113-133`: `r_age` PIPE = 31+EN_CYC bits, EN_CYC taps each a variable-index 1-bit select (121-128); combinational credit (155-168); `rd_data_o = dfi_rddata_i` with no capture register (171-172) so the PHY's data goes straight into the LUTRAM write port. Keep; 34 LUT measured.

## 4. Ranked list

1. Rewrite `gaxi_skid_buffer` DEPTH=2 as a two-register skid without data reset: ~3k LUT chip-wide, ~140 in this slice. Lowest risk, highest yield; one primitive, 49 instances.
2. Ring shadow tracking: delete the return-time shadow-ready sweep (exact), drop the `r_src` reset value, delete dead `r_resp`: ~150-250 LUT, 384 async-set pins, shorter return-fill path.
3. `NARROW_EN=0` on the board netlist (or register the rewrite): avoids ~250-350 LUT and a new comb chain through the host edge before it is ever measured.
4. Address mapper: constant `bank_lsb` on the board or registered mask decode: est. 100-200 LUT across two instances (unverified by the hierarchy report).
5. `fifo_control` flags from registered pointers: timing only (the current WNS path), negligible LUT.
6. Order FIFO 72 -> 64 when HAS_SNARF=0: ~20-40 LUTRAM.
7. (pumice, CDC on) rd async FIFO 64 x 67 to a BRAM dual-clock FIFO: ~130 LUT for one RAMB36.

## 5. Correctness / FPGA smells

5.1 **CDC: token and data cross on separate synchronizers** (`mc_dfi_cdc.sv:105-112,153-188`, async branch only). The comment claims the staged token "is never visible on dfi_clk before the data is" because both go through "the same N_FLOP_CROSS synchronizer". They go through two DIFFERENT 2-flop synchronizers on two different Gray pointers; two independent synchronizers may resolve a transition one destination cycle apart. If the token leads the data by a cycle, `mc_dfi_cmd_path` accepts the WR (`wr_op_ready_i`, 224) and `wr_fire` arms the serializer, whose `w_drive` then waits on `wd_valid_i` (`mc_dfi_wr_serializer.sv:98`) and drives `dfi_wrdata` one DFI cycle late relative to `t_phy_wrlat` (=1 on the board). Not reachable in the board build (DFI_CDC_EN=0), reachable in any true two-clock build. Fix: carry `last` in the wd FIFO payload (it already is the MSB, `mc_dfi_2p1_plane.sv:260`) and count staged bursts on the dfi side from the single data FIFO, deleting `u_wtok_fifo`.

5.2 **No `ASYNC_REG` on the synchronizer flops** (`glitch_free_n_dff_arn.sv:339-350`). Attribute exists only in a comment (232-240). Add it; otherwise placement may split the two stages and `report_cdc` cannot mark the Gray crossings safe.

5.3 **Same-clock branch reads across named domains** (`mc_dfi_cdc.sv:357-364`): `pinit_start_o` is clocked by `dfi_clk` and samples `init_start_i` (ctl domain) directly; legal only because the two clock ports are one net (documented at 46-56). There is no elaboration or constraint check; a build with DFI_CDC_EN=0 and separate clocks would be a silent CDC violation. A `$error` on a parameter the top must set (`SAME_CLK_ASSERTED`) or a Vivado `set_property` check would make it fail loudly.

5.4 **Async-reset flops holding per-entry constants** (`mc_rd_return_ring.sv:273`): 384 FDPE/FDCE with mixed set/reset values for a value that is dead at reset.

5.5 **Combinational host-edge chains with NARROW_EN=1** (`mc_axi4_narrow_pack.sv:195-205,250-268,350-352,403-404`): AW valid gates W ready in the same cycle; AW/AR fields are rewritten with a variable shift and add in zero cycles; downstream `m_awready`/`m_wready`/`m_rready` feed back combinationally to the host. No loop found (each ready depends only on downstream readies and registered state), but it adds 3-4 LUT levels to every host channel at 100 MHz and has never been through a board build.

5.6 **FIFO flags on the producer's valid cone** (`gaxi_fifo_sync.sv:122-125`): the current WNS path (0.021 ns) is CSR -> scheduler -> `rd_iss_valid` -> `u_issue_q` flag flop (`timing_worst.txt:15-22`). Not a bug, but the FIFO offers no timing isolation.

No latch inference (0 "Register as Latch", `utilization_impl.txt:42`), no combinational loop found in the ring/intake/narrow handshakes (checked `drain_valid_o`/`w_ft`/`w_room` at `mc_rd_return_ring.sv:224-244`: `w_ft` uses `r_credits` not `w_room`, and `drain_ready_i` from `mc_rd_intake.sv:567-568` does not depend on `drain_valid`). No async reset released into a RAM: all RAM arrays are reset-free.

## 6. Keep as-is

- `mc_rd_return_ring` core (BRAM + ticket FIFO + `r_ready` vector + fetch pointer + 2-deep prefetch skid): already the FPGA-native reorder structure; it reorders by ticket write address, not by search.
- `mc_dfi_cmd_path`, `mc_xddr2_cmd_formatter`, `mc_dfi_wr_serializer`, `mc_dfi_rd_aligner`: 43 LUT total on the board, registered outputs, delay-line timing. Nothing to gain.
- `mc_axi_burst_chopper` / `mc_wr_splitter`: counters and one adder each, FSM-free.
- `gaxi_fifo_sync` / `gaxi_fifo_async` memories: unreset, enable-written, LUTRAM-inferred; correct for these depths. Only the output-register reset and the next-pointer flags are worth touching.
- `mc_rd_intake` AR stage register and the `RD_FIFO_DEPTH=0` / `WDATA_FIFO_DEPTH=0` bypasses (`mc_rd_intake.sv:592-597`, `mc_wr_intake.sv:414-419`): already removed redundant buffering on the board.
- Gray-pointer async FIFO structure (when CDC is on): standard and sound apart from 5.1/5.2.

## 7. Measurement caveats
- Vivado's post-route hierarchical utilization re-attributes logic after cross-boundary optimization: `u_issue_q` 125 logic LUT for a 64x6 FIFO and `u_rd_intake` own-logic 17 LUT (holding two barrel shifters' worth of mapper) are both implausible in isolation. Per-structure LUT numbers above are given at the parent level where they are trustworthy and marked "est." otherwise.
- The 10-29 build predates RET_BYPASS/FALLTHRU/CMD_FALLTHRU (10-31) and the narrow pack (11-03); the next board build will carry roughly +64-bit 2:1 drain mux x2 in the ring, +34-bit mux in the cmd FIFO, and the narrow pack.
