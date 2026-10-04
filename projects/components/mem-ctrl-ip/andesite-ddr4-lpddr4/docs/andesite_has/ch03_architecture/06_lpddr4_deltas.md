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

# The LPDDR4 Deltas, Chapter by Chapter

This book is DDR4-led with LPDDR4 carried per-chapter, the same one-book-
both-memtypes shape scoria uses. This chapter collects LPDDR4's deltas as a
reading aid — each entry points at the chapter that owns it, and none of them
contradicts what that chapter says.

## Where LPDDR4 differs

**No bank groups.** LPDDR4's 8 banks per channel stand ungrouped
(JESD209-4). The long/short pair the scheduler learns for DDR4 degenerates to
L = S, and the requirement on the arbiter and global timers is graceful
degeneration, not a special case: same-group and cross-group checks collapse
into one constraint per pair. Chapter 3.1.

**Two x16 channels per package.** LPDDR4 devices offer a pair of independent
x16 channels. The design point exercises one channel (Chapter 2.4); the
second channel is a build parameter, and the per-channel state that
`ca_train_ifc` and the LPDDR4 refresh path already carry is why that
parameter doesn't restructure anything. Chapter 2.4, 3.3.

**The 6-bit DDR CA bus.** LPDDR4 commands ride a 6-bit double-data-rate CA
bus, two cycles per command, with a different encoding philosophy from
DDR4's five-pin + address form. This is the formatter's NEW LPDDR4 CA
submodule, kept beside — not merged into — the DDR4 path so each stays
reviewable. Chapter 3.2.

**MPC instead of ZQ opcodes.** Calibration, training entry, and several
feature modes ride the multipurpose command rather than dedicated opcodes.
`zq_ctrl`'s NEW MPC submodule and `ca_train_ifc` share the issuer. Chapters
3.2, 3.3.

**Controller-directed per-bank refresh.** LPDDR4's per-bank refresh names
the bank, replacing scoria's rotor with explicit bank scheduling and making
the advanced schemes of andesite TASK-001's survey implementable. This
edition implements the commodity round-robin. Chapter 3.4.

**MR-programmed termination.** No ODT pin; DQ ODT is programmed in the mode
register set and held static this edition. The dynamic machinery of
`odt_ctrl` is DDR4-scoped. Chapter 3.5.

**DSM power states.** Deep-sleep modes exist in the standard and are
deferred here with the condition named in Chapter 3.1 — they wake the
`powerdown_ctrl`/`dfi_signal_pack` pair and need a target that can measure
power. Chapter 3.1.

**Training.** CA bus training and write-DQ calibration are LPDDR4-native
requirements, carried by `ca_train_ifc` with firmware searches. Chapter 3.3.

**Init.** LPDDR4's initialization is its own ordered sequence — bus-carried
reset, mode-register writes in JESD209-4's order, MPC ZQ calibration — with
the same binding rule as DDR4's: the order is a citation, not a design
choice. Chapter 3.2.

**Inline CKE.** LPDDR4 has no dedicated `CKE` pin; the CKE-equivalent
state is encoded on the CA bus, so power-down and self-refresh entry are
CA-bus transactions rather than a separate pin. The formatter's `dfi_cke`
output is DDR4-scoped; the LPDDR4 CA submodule handles CKE-equivalent
states. Chapter 3.2 (MAS `ch02_blocks/01_cmd_formatter.md`).

## What LPDDR4 does *not* change

Worth stating to keep the scope honest: the host side (nothing about LPDDR4
reaches the AXI4 front end), the datapath structure (the same read/write
pipelines serve both memtypes; only the DBI pin handling is DDR4-side), the
bank-timer and CAM machinery, and the evidentiary discipline. The family
engine covers both memtypes because the deltas are concentrated where they
should be: the command encoding, init/training, refresh policy, and
termination.
