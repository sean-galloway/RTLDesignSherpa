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

# What Is Inherited, and the Blocks That Change

## The inheritance, stated once

Twenty-one of pumice's twenty-four FUBs carry over with no functional change, as
do the top, core, AXI4 macro and the DFI datapath. Chapter 2.3 lists them. This
chapter covers only what changes, and the list is short by design.

**The inheritance is an argument, not a convenience.** Those blocks have been
through board bring-up, a read-path rebuild that took reads from 291.7 to
571.3 MB/s, and a formal campaign across nine modules. Re-deriving them would
discard that evidence and reintroduce the bugs it caught.

**Important — inherit `global_timers` in its FIXED form.** pumice's version
published readiness one cycle late: the registered status flop sampled the
current counter state rather than the next, so the flags alone permitted tCCD
and tRTW violations. The fix computes one next-state function and feeds both the
counter and its status flop from it. A fresh implementation written from a
behavioural description of the same block would reintroduce the defect, because
the description does not mention the flop. Copy the module.

## The changes, in one table

| Block | Marking | Cause | Where |
|---|---|---|---|
| `init_sequencer` | MODIFIED | `RESET#` is a pin; MR order is MR2-MR3-MR1-MR0; ZQCL closes init | 3.2 |
| `mode_register` | MODIFIED | MR0-MR3 replaces MR0-MR2 plus EMRS3 | 3.2 |
| `dfi_cmd_formatter` | MODIFIED | new encodings: `ZQCL`, `ZQCS`, `PREA` | 3.2 |
| `scoria_zq_ctrl` | **NEW** | periodic `ZQCS` is maintenance traffic | 3.2 |
| `scoria_wrlvl_ifc` | **NEW** | DDR3 adds write leveling | 3.3 |
| `refresh_ctrl` | INHERITED | pumice already implements `REFpb`; LPDDR3 uses the same device-fixed mechanism. Only a mode-select CSR is added | 3.4 |
| `powerdown_ctrl` | INHERITED | mechanism unchanged: CKE + `SRE`/`SRX`. The DFI low-power channel is unused on this PHY family | below |
| `dfi_signal_pack` | INHERITED | every signal it packs is identical in v2.1.1 and v3.1 for DDR3; v3.1's new channels are driven at the layer above | Ch 4.1 |
| `scoria_mem_cmd_scheduler` | MODIFIED | must admit ZQ demand alongside refresh | 3.2 |
| `scoria_csr` | MODIFIED | new timing registers and leveling telemetry | Ch 5 |

: Table 3.1: Every change, with its cause

## Power-down: smaller than v0.1 thought

DDR3 and LPDDR3 both offer precharge-power-down, active-power-down and
self-refresh (`SRE` / `SRX`). pumice's `powerdown_ctrl` already implements
idle-timer-driven entry and exit, and **that is the whole mechanism** on a
Series-7 PHY target.

v0.1 through v0.3 of this document said the interesting change was that DFI
v3.1 splits `dfi_lp_req` into `dfi_lp_ctrl_req` and `dfi_lp_data_req`, and left
the exit-ordering as an open question. The split is real, but it is not
load-bearing here: **`s7ddrphy` implements no DFI low-power interface at all**,
and LiteDRAM's generated DDR3 controller does not drive one either — zero
`dfi_lp` hits in the generated core against 92 references to `CKE`.

Power-down on this PHY family is a **DRAM command** matter: CKE, plus `SRE` and
`SRX` for self-refresh. `powerdown_ctrl` is therefore INHERITED in mechanism,
and what it gains for DDR3 is the new self-refresh command encodings rather
than a new interface.

**Status, 2026-09-30: not in the design, by decision (Sean).** The module is
INHERITED as a FILE; nothing instantiates it, and `scoria_top` has no CKE port
at all -- so the feature is absent rather than unconnected, and the DRAM simply
never leaves normal operation. That matches the reference: LiteDRAM's generated
DDR3 core for this board has **no power-down or self-refresh engine of any
kind**. Its only `power_down` references are the MMCM's `PWRDWN` pin, and the
92 `CKE` references resolve to a CSR bit --
`main_litedramcore_sdram_cke = main_litedramcore_sdram_storage[1]`, fanned
identically to all four phases -- i.e. software raises CKE during init and it
stays raised. There is no `SRE`/`SRX` issue path.

So scoria holding CKE high for ever is parity with the controller that passes
memtest on this hardware, not a shortfall against it. The same applies to
`dfi_signal_pack`, also INHERITED-as-a-file and also uninstantiated: every DFI
bus here is phase-multiplied by construction (`DFI_ADDR_BUS_W = ROW_WIDTH *
DFI_RATE`, and so on) and LiteDRAM's `dfi_p0..p3_*` are per-phase for the same
reason, so there is no packing step for either design to perform.

**That justification is DDR3-scoped, and does not transfer to LPDDR3.** The
argument above is parity with a DDR3 reference; LiteDRAM's DDR3 core says
nothing about what an LPDDR3 part needs. LPDDR exists FOR power: self-refresh
is a mobile part's normal idle state rather than an exotic mode, and LPDDR3
adds **Deep Power Down**, which DDR3 does not have -- `scoria_pkg` already
marks `OP_DPDE` "LPDDR3 only". DPD requires stopping the DRAM clock, which is
`dfi_dram_clk_disable_o`, and that signal is `dfi_signal_pack`'s one function
NOT covered by the phase-multiplied buses. `powerdown_ctrl`'s own v3 TODO names
the dependency: DPD entry "needs `dfi_dram_clk_disable_o` cooperation from
scoria_dfi_signal_pack". So for LPDDR3 the two are a PAIR, and both are
load-bearing.

What stands in the way is four gaps, not one wire:

| Level | State today |
|---|---|
| `powerdown_ctrl` / `dfi_signal_pack` | not instantiated |
| `scoria_top` / `scoria_dfi_layer` | no `dfi_cke` or `dfi_dram_clk_disable` port at all |
| `scoria_dfi_cmd_formatter` | `OP_SREFE` / `OP_SREFX` / `OP_DPDE` fall to the `default:` arm and are driven as NOP |
| `scoria_cmd_arbiter` | never picks any of those three ops |

So the decision stands for the DDR3 target and must be re-made on LPDDR3's own
terms the moment an LPDDR3 device is in scope. It also tips the housekeeping
question: these two files are the starting point for that work, so keeping them
dormant is worth more than deleting them. See scoria-ddr3-lpddr3 TASK-003.

**Requirement for the DFI low-power ports.** scoria still exposes
`dfi_lp_ctrl_req` and `dfi_lp_data_req`, because DFI v3.1 defines them and a
future PHY may consume them. Their behaviour when no acknowledgement ever
arrives is specified: **time out and report; never block power-down.** An
unacknowledged request must not be able to wedge the controller — which is the
real hazard, and a smaller one than the ordering puzzle v0.2 imagined.
