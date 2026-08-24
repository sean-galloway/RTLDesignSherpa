<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Closed (done)

---

## PUMICE-002 — test_pumice_top_csr wr_rd roundtrip returns zero read beats
**Status:** closed 2026-08-24 — TEST defect, not RTL: stale hand-packed DFI_PHASE

`cocotb_test_pumice_top_csr` fails its AXI write-then-read phase: read 0 gets
ZERO R beats in 800 cycles (`got=[]`), i.e. the read path never returns — while
`test_pumice_top` (45 read-heavy tests), core, core_dfi, geared and the whole
fub/macro suite pass.

**Bisected 2026-07-21:** fails identically at HEAD (95c9490a) with only the
filelist fix applied — predates the deskew removal and the refresh/tRFC arbiter
change.

**Re-confirmed 2026-07-23:** fails identically with `pumice_top.sv` reverted to
HEAD and a clean rebuild, so it is not caused by the PUMICE-001 page_policy fix
either. Note the rebuild mattered — the first run reused a stale `sim_build`
and completed in 0.41 s, which would have made a reverted-RTL run meaningless.

Suspect the CSR-programmed config path (hwif-driven init) diverging from the
TB-driven config the other tops use. The top tests were compile-broken (missing
`gaxi_fifo_async` deps in the dv/tb filelists) for some window, so the
regression that introduced this was masked.

**Root cause (2026-08-24):** the test programs CSRs by HARDCODED offset +
hand-packed bit positions (predates [[registers-by-name]]). `DFI_PHASE` grew
`gear_ratio[8:7]` and `bl[12:9]` when gear/BL became runtime CSRs — during the
exact filelist-drift window this test could not compile — and the test's
`pk((0,0),(0,4))` kept writing the whole register as 0. gear=0/bl=0 programs a
zero-beat burst: init completes, AXI writes still get B responses, but the read
path has nothing to return → rvalid never fires → `got=[]`. Every register
OFFSET still matched the current regmap; only the field packing had rotted.

**Fix:** write `gear_ratio=log2(DFI_RATE)`, `bl=BL` in the DFI_PHASE pack
(one line). Red→green flip confirmed on clean builds. The suspicion in the
original filing ("CSR-programmed config path diverging from TB-driven") was
half right — the divergence was in the TEST's packing, not the RTL's hwif.
Textbook case for [[registers-by-name]]: the by-name TB absorbed the RDL
change, the hardcoded one silently rotted. Follow-up candidate: migrate this
test's CSR writes to the generated regmap so it cannot rot again (its distinct
value — raw-cpuif programming + hand-rolled AXI as a BFM-independent second
opinion — is worth keeping).


## PUMICE-005 — Board reads WORK: validated tuple + honest measurement
**Status:** closed 2026-07-21 — reads clean on silicon; residual corruption split out to PUMICE-004

The rate-2/BL4 board (BUILD_ID 0x44445232) reads CLEAN. The blocker was never
the analog read path; it was three stacked measurement/config defects:

1. **Sweep axis.** s7ddrphy asserts `rddata_valid` a FIXED `read_latency`
   (= cl_sys+6 = 8) sys cycles after `rddata_en` (pure delay line; ISERDES
   capture is continuous), so for reads `t_rddata_en` only places valid. The
   DATA arrives at its own physical latency — `DFI_TUNING.rddata_delay` slides
   the data onto the valid window. Every failed sweep held rddata_delay=0 where
   alignment is unreachable. **Validated tuple: t_phy_wrlat=1, t_rddata_en=6,
   rddata_delay=7, bitslip=0, IDELAY tap 8 (eye taps 0..16, width 17).** Baked
   into the A7Leveling ctor defaults.
2. **False-pass metric.** `wait_engine` default bails when rd_error latches (a
   mismatch latches it) -> `beats_mismatched` read EARLY; and a HUNG read counts
   nothing -> reads back 0 = fake clean. Fixed in bringup_joint_probe /
   `A7Leveling._test` / train_per_lane (ignore_error=True + require done; hang
   reported distinctly).
3. **RMW poison.** On pre-CDC-fix bitstreams the pumice APB window returns a
   PRIOR transaction's data, so every `rmw=True` write spliced stale garbage
   into preserved fields (set_deskew after set_controller_cfg silently reverted
   wrlat/rden -> leveling swept at reset timing). pumice_device now NEVER rmws:
   shadowed full-word writes seeded from RDL resets, `invalidate_shadow()` on
   soft_reset. (RTL CDC fix already landed in `apb4_slave_cdc`; bitstreams in
   `bitstream/` predate it — rebuild to retire the hazard on-silicon.)

Residual intermittent row-sized (256-beat/2KB) read corruption, strongly
refresh-correlated (soak A/B: tREFI default 0/8 dirty, tREFI=0x40 4/4 dirty at
~32-44/1024 beats, tREFI=0xFFFF 0/8) is a separate defect — split out to
PUMICE-004, now confirmed on silicon.

## PUMICE-009 — Generic AXI data-width gearing
**Status:** closed — resolved via external converter

Make host `AXI_DATA_WIDTH` a free parameter (32/64/128/256/512) decoupled from
the core width `DW = DRAM_BEAT_WIDTH x DFI_RATE`. Family-wide
(DDR2/3/4/LPDDR2), for future DDR* IP where each device/PHY pins its own
(beat, rate) but the host SoC wants a fixed convenient AXI width.

Implemented via the EXTERNAL formally-verified `axi4_dwidth_converter_wr/_rd`
in a wrapper `rtl/top/pumice_top_geared.sv` (host width <-> DW; GEAR-1 =
generate bypass, bit-identical). Core datapath untouched. Verified end-to-end
(`test_pumice_top_geared.py`): write bursts at host in {64, 128, 256}
round-trip back through host-width reads (down-gear / bypass / up-gear).

Chose external over the internal gearbox because the datapath was freshly
stabilized and the converters are already formal; also the rearchitecture
already solved the original a7ddrphy forcing function (AXI = beat x rate = 128,
a fine width — no gearing needed for the board).

Design + rationale + deferred internal-gearbox option:
`docs/AXI_DRAM_GEARING_SCOPE.md`

## PUMICE-010 — Single-register AXI-address -> {bank,row,col} mapping
**Status:** closed — resolved

`addr_mapper.sv` is now driven by ONE knob — `ADDR_MAP.bank_lsb` (the CSR
register that replaced the old scheme selector) — plus an optional bank
XOR-hash (`ADDR_MAP.hash_en`/`hash_seed`). The mapping is derived by stacking
fields around the bank position: `col_lo(bank_lsb) | bank | col_hi | row | rank`,
row LSB invariant at `CW+BW`. The classic schemes are just settings, no scheme
mux: `bank_lsb == COL_WIDTH` = ROW_MAJOR; `bank_lsb == log2(cols/burst)` = max
BANK_INTERLEAVE (burst locality preserved by col_lo); `hash_en` = XOR_HASH on
top.

Landed: RDL ADDR_MAP register (regenerated CSR + regmap via
`bin/peakrdl_generate.py`); addr_mapper rewritten (single stacked extraction +
hash, 3 generate blocks + mux gone); bank_lsb/hash_en/hash_seed threaded through
pumice_axi4_ifc / wr+rd intakes / pumice_core / pumice_top (driven from
`hwif_out.ADDR_MAP`); program_defaults + test_pumice_top_csr + core tests
updated. FUB conformance (`test_addr_mapper`) rewritten to sweep bank_lsb across
[0, COL_WIDTH] + hash on/off vs a Python reference — 5/5. Full suite: 407 pass,
0 fail (macro 141 + fub/top 266).

`addr_map_scheme_e` retained only for the retired OLD macro sentinels
(pumice_core_macro / axi_frontend_macro / pumice_config_block), which were
carried to the new intake interface — candidates for future retirement.

## PUMICE-011 — Full LPDDR2 mode-register init
**Status:** closed — resolved

Implemented the JEDEC JESD209-2F LPDDR2 init sequence in `init_sequencer.sv`
(memtype-gated): MRW Reset(MR63) -> ZQ Init(MR10=0xFF) -> MR1(BL8/nWR3=0x23) ->
MR2(RL3/WL1=0x01) -> MR3(DS 40ohm=0x02). The wide MR index (MA up to MR63)
reaches the CA formatter via the ROW request field packed as {MA[5:0], OP[7:0]}
(`dfi_cmd_formatter` unpacks row[13:8]=MA, row[7:0]=OP) — no 3-bit bank-port
limit. Only MR1/2/3 update the CL/CWL/BL shadow; MR63/MR10 are issued but not
shadowed. `mode_register.sv` LPDDR2 CL/CWL decode made JEDEC-faithful (MR2[3:0]
RL&WL enum).

Verified: DFISlavePHY now records decoded MRW ({index:data}); `smoke_lpddr2`
asserts init programmed {63:0x00, 10:0xFF, 1:0x23, 2:0x01, 3:0x02}. Formatter
conformance + init_sequencer FUB updated.

**NOTE (silicon):** the sim gates PHY-init-complete on config-ready (TB) so the
sequencer latches the correct memtype ("config before init"). Real LPDDR2
silicon needs memtype stable before init — a strap, or gating the sequencer's
start on `CTRL.init_start`. DDR2 (the board target) is unaffected: its reset
default IS DDR2.

## PUMICE-012 — LPDDR2 write-auto-precharge dropped writes
**Status:** closed — resolved (RDS-DV DFISlavePHY fix)

`workload_mix_lpddr2` had dropped writes under LPDDR2's HAPPY_HYBRID row-miss
policy, which issues WRA (write-auto-precharge). Root cause was NOT the CA
encoding or write cadence: the DFI slave `_handle_command` had branches for
WR/RD but none for WRA/RDA. DDR2's decoder never returns WRA/RDA (it returns
WR/RD and carries auto-precharge in addr bit 10), but the bit-exact LPDDR2 CA
decoder folds AP into the opcode -> returns WRA/RDA -> fell through -> no
pending write -> `wrdata_en` became "stray data beats" and the write was
silently dropped.

Fix: fold WRA->WR and RDA->RD in `_handle_command` (auto-precharge already
carried in addr bit 10 for both paths). All LPDDR2 traffic tests now pass;
xfail removed.
