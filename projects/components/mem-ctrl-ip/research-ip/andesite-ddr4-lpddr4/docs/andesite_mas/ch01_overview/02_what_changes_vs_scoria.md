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

# What Changes vs scoria

The complete marking set, copied from the HAS (Ch 2.3 and Table 3.1) rather
than re-derived. This table and the HAS carry the same pairs; the Task-10
consistency gate diffs them mechanically.

| scoria module | Marking | What changes, one line |
|---|---|---|
| `scoria_top` | INHERITED | structure unchanged |
| `scoria_top_geared` | INHERITED | the width-gearing wrapper, unchanged |
| `scoria_core` | INHERITED | core assembly unchanged |
| `scoria_axi4_ifc` | INHERITED | the AXI4 host side is untouched by this generation |
| `scoria_mem_cmd_scheduler` | MODIFIED | L/S admission alongside scoria's ZQ maintenance admission |
| `scoria_dfi_layer` | MODIFIED | DFI 4.0 control surface and DBI wires |
| `scoria_addr_mapper` | MODIFIED | bank-group decode: BG0/BG1 between chip select, bank and row |
| `scoria_cmd_arbiter` | MODIFIED | L/S-aware issue on the same-group / cross-group split |
| `scoria_global_timers` | MODIFIED | tCCD_L/S and tRRD_L/S as first-class counters |
| `scoria_dfi_cmd_formatter` | MODIFIED | ACT_n fifth pin, BG0/BG1, CA parity; NEW submodule: LPDDR4 6-bit CA path |
| `scoria_init_sequencer` | MODIFIED | DDR4 reset procedure, MR3-MR6-MR5-MR4-MR2-MR1-MR0 order, gear-down entry, parity enable |
| `scoria_mode_register` | MODIFIED | MR0-MR6 field maps per memtype |
| `scoria_zq_ctrl` | INHERITED | DDR4's ZQCS/ZQCL exactly as built; NEW submodule: LPDDR4 MPC calibration |
| `scoria_refresh_ctrl` | MODIFIED | FGR 1x/2x/4x on the inherited elastic/TCR/placement base |
| `scoria_dfi_cmd_path` | MODIFIED | ACT_n, BG and parity wires ride the command path |
| `scoria_dfi_rd_aligner` | MODIFIED | DBI read path |
| `scoria_dfi_wr_serializer` | MODIFIED | DBI write path |
| `scoria_wrlvl_ifc` | MODIFIED | training-interface family grows; contract and no-search rule unchanged |
| `scoria_powerdown_ctrl` | DORMANT | carried dormant, waking condition in HAS Ch 3.1 |
| `scoria_dfi_signal_pack` | DORMANT | carried dormant, waking condition in HAS Ch 3.1 |
| (new) `odt_ctrl` | NEW | dynamic ODT: RTT_NOM/WR/PARK and the ODT latency family |
| (new) `rdlvl_ifc` | NEW | MPR-based read-leveling interface, no search loop |
| (new) `ca_train_ifc` | NEW | LPDDR4 CA/WDQ training interface, no search loop |

: Table 1.3: The marking set, copied from the HAS

## One paragraph per chapter page

**Command formatter (MODIFIED / NEW).** The wire-level truth table changes
shape: ACT becomes a five-pin command, BG0/BG1 appear on the activate's
address pins, and parity rides the command stream. The LPDDR4 side is a new
6-bit double-data-rate CA encoding, two cycles per command — a submodule so
the DDR4 path stays reviewable on its own. Mechanism detail: Ch 2.1.

**Init sequencer (MODIFIED).** The FSM grows DDR4's reset-procedure states
and gear-down entry, and programs parity enable in the MR order. The order
remains JEDEC's, now MR3-MR6-MR5-MR4-MR2-MR1-MR0; the MAS page lists the
states and the waits by name, with values per the HAS's Q1 recording.
Mechanism detail: Ch 2.2.

**Mode register (MODIFIED).** MR0-MR6 for DDR4 and the LPDDR4 MR set, field
maps per memtype, with the MAS page carrying the field-level tables the HAS
deliberately leaves to this book. Mechanism detail: Ch 2.3.

**Address mapper (MODIFIED).** One bounded change: the decode grows BG0/BG1
between chip select, bank and row. The decode equations are the kmap book's
first address-map targets. Mechanism detail: Ch 2.4.

**Scheduler and arbiter (MODIFIED).** L/S-aware issue: the arbiter consults
same-group versus cross-group spacing, the global timers carry the long/short
pairs, and maintenance admission (refresh, ZQ, ODT turnarounds) rides the
inherited request/grant channel. LPDDR4 degenerates L = S gracefully.
Mechanism detail: Ch 2.5.

**Refresh controller (MODIFIED).** FGR 1x/2x/4x via the MR3 image, interval
arithmetic scaled per factor, and LPDDR4's controller-named per-bank
scheduling replacing the rotor. The elastic/TCR/placement policy base is
inherited intact. Mechanism detail: Ch 2.6.

**ZQ controller (INHERITED / NEW).** The DDR4 core is scoria's, unchanged.
The new submodule sequences LPDDR4 calibration through MPC. Mechanism
detail: Ch 2.7.

**ODT controller (NEW).** The policy block: RTT_NOM/WR/PARK selection on the
command-stream tap, ODT pin latency enforcement, rank coupling for
multi-rank builds. LPDDR4's MR-programmed termination is init-side, not this
page's. Mechanism detail: Ch 2.8.

**Training interfaces (MODIFIED / NEW).** `wrlvl_ifc` keeps its contract;
`rdlvl_ifc` and `ca_train_ifc` are new pages in the same family — handshake,
MR/MPC path, windows, four-state telemetry, no search loops anywhere.
Mechanism detail: Ch 2.9.

**DFI datapath (MODIFIED).** `dfi_cmd_path` widens for ACT_n/BG/parity; the
aligner and serializer pass DBI through; the layer presents the 4.0 control
surface. The CDC and the pack stage are inherited (the latter dormant).
Mechanism detail: Ch 2.10.
