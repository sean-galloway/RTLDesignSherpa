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

# What Changes vs pumice

The complete marking set, copied from the HAS (Ch 3, Table 3.1) rather than
re-derived. Family doctrine 4 makes the markings a contract: this table, the
HAS's, and the inventory on the previous page carry the same pairs, and a
drift in any of them is a defect.

| Block | Marking | Cause | MAS page |
|---|---|---|---|
| `scoria_top` / `scoria_top_geared` / `scoria_core` | INHERITED | structure unchanged | 2.1-2.3 |
| `scoria_axi4_layer` | INHERITED | the AXI4 host side is untouched by this generation | 2.1 |
| `scoria_scheduler_layer` | MODIFIED | must admit ZQ maintenance demand alongside refresh | 2.2 |
| `scoria_dfi_layer` | MODIFIED | DFI v3.1 control surface (per-data-phase CS, write-leveling handshake) | 2.3 |
| `scoria_init_sequencer` | MODIFIED | `RESET#` is a pin; MR order is MR2-MR3-MR1-MR0; ZQCL closes init | 2.18 |
| `scoria_mode_register` | MODIFIED | MR0-MR3 replaces MR0-MR2 plus EMRS3 | 2.19 |
| `scoria_dfi_cmd_formatter` | MODIFIED | new encodings: `ZQCL`, `ZQCS`, `PREA` | 2.22 |
| `scoria_refresh_ctrl` | MODIFIED (v0.9) | the `REFpb` rotor and the JEDEC ±8 credit accumulator are inherited; TASK-001 Modes A/B (elastic pull-in/postpone streaks, TCR tREFI derate) are real changes behind CSRs | 2.16 |
| `scoria_zq_ctrl` | **NEW** | periodic `ZQCS` is maintenance traffic; carries the CSR-selectable placement policy (TASK-001 Mode C) | 2.17 |
| `scoria_wrlvl_ifc` | **NEW** | DDR3 adds write leveling; the interface, not the search | 2.20 |
| `scoria_powerdown_ctrl` | INHERITED (dormant) | mechanism unchanged: CKE + `SRE`/`SRX`; not instantiated, by decision | 2.26 |
| `scoria_dfi_signal_pack` | INHERITED (dormant) | every signal it packs is unchanged for DDR3; its v3.1 new channels are driven at the layer above | 2.26 |
| everything else (20 FUBs: CAMs, intakes, timers, arbiter, splitter, chopper, mappers, CDC, serdes, aligner, cmd_path) | INHERITED | no functional change; see the inventory table for the full list | 2.4-2.15, 2.21, 2.23-2.25 |

: Table 1.3: The marking set, copied from the HAS

## What the MAS adds to the marking

The HAS states the markings; this book is where the marked blocks live at
signal level. Three additions are worth calling out on this page because they
are easy to miss inside the chapter pages.

**The MC-001 rename.** The macro tier no longer uses pumice's naming:
`scoria_axi4_ifc` is now `scoria_axi4_layer` and `scoria_mem_cmd_scheduler`
is now `scoria_scheduler_layer` (trunk commit `3eee953d2`, the scoria half of
the family-wide MC-001 convention). Older family documents — including parts
of andesite's MAS — still cite the old names; the mapping is one-to-one and
nothing else about the blocks changed in the rename.

**`global_timers` is inherited in its FIXED form.** pumice's original
published readiness one cycle late: the registered status flop sampled the
current counter state rather than the next, so the flags alone permitted tCCD
and tRTW violations. The fix computes one next-state function and feeds both
the counter and its status flop from it. This is not a cosmetic detail — a
fresh implementation written from a behavioral description reintroduces the
defect, because the description does not mention the flop. The page for the
block (2.14) states the invariant as a contract; the formal proof
(`formal/scoria/scoria_global_timers.sby`) closes it.

**The dormant pair is a decision, not dead code.** `powerdown_ctrl` and
`dfi_signal_pack` stay in the tree uninstantiated because they are the
declared starting point for LPDDR3 power-down work (self-refresh is a mobile
part's normal idle state, and deep power-down needs the pair together). The
DDR3-scoped justification — parity with the LiteDRAM reference, which has no
power-down engine at all — does not transfer to LPDDR3. Page 2.26 carries the
four-gap table that stands between today and that wake-up.

## One paragraph per changed or new block

**Scheduler layer (MODIFIED).** The change is one extra maintenance source at
the arbiter: ZQ requests and waits on the same request/grant terms refresh
always had (family doctrine 2 — request and wait, never preempt). Everything
else about the macro is pumice's scheduler with DDR3's timings. Page 2.2.

**Init sequencer (MODIFIED).** DDR3 brings a `RESET#` pin and a four-register
MR set; the FSM walks RESET# low → CKE → tXPR → MR2 → MR3 → MR1 (DLL enable)
→ MR0 (DLL reset) → ZQCL → tDLLK/tZQinit. LPDDR3 walks MRW MR63 → MRW MR10 →
MR1 → MR2 → MR3. Page 2.18.

**Mode register (MODIFIED).** MR0-MR3 shadows per rank with live decode of
CL/CWL/BL/AL/WR; the RTL comment resolving JESD79-3F's prose-versus-Figure-9
inconsistency in favor of the figure is preserved verbatim on the page. Page
2.19.

**Command formatter (MODIFIED).** Three new encodings — `ZQCL`, `ZQCS`,
`PREA` — join the inherited table, and the LPDDR3 side is the JESD209-2F
Table 60 CA bus. Page 2.22.

**Refresh controller (MODIFIED, v0.9).** The inherited rotor and credit
machine stand; TASK-001 adds elastic demand-aware pull-in/postpone (Mode A)
and the TCR tREFI derate (Mode B), both CSR-gated and off by default. Page
2.16.

**ZQ controller (NEW).** Periodic `ZQCS` as ordinary maintenance traffic —
interval CSR, request/grant to the arbiter, post-grant tZQCS hold, and the
Mode C defer-under-demand placement policy. Page 2.17.

**Write-leveling interface (NEW).** Decision D2 in silicon: firmware drives
the search; the RTL provides the DFI v3.1 leveling handshake, the MR1 write
path, the `tWL*` window enforcement, and four-state telemetry. No delay-walk
states exist anywhere in the block. Page 2.20.
