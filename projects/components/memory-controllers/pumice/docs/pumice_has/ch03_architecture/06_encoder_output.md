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

# Command Encoder and Gear Output

This section covers the two modules that translate the controller's internal generic command bus into DFI wire signals: `cmd_encoder` (memtype-specific wire mapping) and `gear_out` (1-phase to N-phase replication).

## `cmd_encoder`

### Purpose

Translate the controller's internal generic command record into the DFI wire signals appropriate for the target memory. The encoder is the only place where DDR2 and LPDDR2 differ at the wire layer.

### Input Record

The internal generic command is:

```
{
  cmd        : { NOP, DESEL, ACT, RD, WR, RDA, WRA,
                 PRE, PREA, REF, REFPB, MRS, ZQCS, ZQCL },
  bank       : log2(NUM_BANKS),
  row        : ROW_WIDTH,
  col        : COL_WIDTH,
  ap         : 1,           // auto-precharge bit
  all_banks  : 1,           // all-banks variant of PRE / REF
  mr_addr    : 8,           // MR / EMR address
  mr_data    : 16           // MR / EMR data (LPDDR2 only; DDR2 packs into addr)
}
```

### DDR2 Encoder

Outputs the standard DDR2 command-bus signals per JESD79-2 Table 67:

- `cs_n` — asserted (low) on command issue; high in idle
- `ras_n`, `cas_n`, `we_n` — set per the JESD79-2 lookup table
- `bank` — driven from the command record's `bank` field
- `address` — driven from `row` for ACT; from `col` for RD / WR (with `addr[10]` carrying the AP bit for column commands or the AB bit for PRE)
- `cke` — held high during normal operation; lowered by the power-state FSM
- `odt` — driven from a small lookup based on transaction type
- `reset_n` — DDR2 has no reset_n; held high

### LPDDR2 Encoder

Per DFI v2.1 Table 1, LPDDR2 carries the command on the `dfi_address` 20-bit CA word:

- `cs_n` — asserted on command issue
- `ras_n`, `cas_n`, `we_n`, `bank` — held at their idle values (1, 1, 1, 0)
- `address[19:0]` — packed CA word via the algorithm in our existing `lpddr_ca` encoder (`src/CocoTBFramework/components/dfi/lpddr_ca.py`):
  - `address[9:0]` = CA cycle 1
  - `address[19:10]` = CA cycle 2
- `cke` — used by the power-state FSM (LPDDR2 has the richer CKE state machine)
- `odt` — LPDDR2 has no ODT; held low
- `reset_n` — held high during normal operation

### Memtype Selection

At elaboration, the appropriate encoder is instantiated based on `MEMTYPE`. Only one is synthesized; the other path is dead code.

### Idle Defaults

When the controller is not issuing a command, the encoder drives the bus to its deselected idle state:

- DDR2: `cs_n=1, ras_n=1, cas_n=1, we_n=1, bank=0, address=0, odt=0`
- LPDDR2: `cs_n=1, address=0`

This convention matches the DFI v2.1 Table 2 default values.

### Verification

Per-encoder unit tests:

- DDR2 encoder: round-trip table test against the JESD79-2 truth table
- LPDDR2 encoder: leverages our existing 30 round-trip tests for the CA bus encoder (`tests/unit/test_lpddr_ca.py` in the DV repo)

---

## `gear_out`

### Purpose

Replicate the 1-phase internal command bus onto N parallel DFI output phases, where `N_PHASES ∈ {1, 2, 4}`.

### Behavior

- Phase 0 by convention carries the active command on the cycle it's issued.
- Other phases idle (drive their deselected defaults).
- For `N_PHASES == 1`: pass-through. Synthesis will optimize the module away.
- For `N_PHASES == 2` or `4`: the output stage tracks which phase a command should land on. Some implementations assign the phase based on workload; ours uses the simpler "always phase 0" rule and relies on the PHY to serialize correctly per the DFI frequency-ratio spec.

### Multi-Cycle Commands

LPDDR2's 2-cycle commands are **not** split here. They are packed into a single 20-bit `dfi_address` word by the encoder; the PHY's job is to split them into two DRAM cycles per DFI v2.1 §3.1.

### Phase Naming

Per-phase signals follow the DFI naming convention with `_p0` through `_pN_PHASES-1` suffixes. For `N_PHASES == 1`, the suffix may be elided per DFI v2.1 §3.1 ("phase 0 may exclude the suffix"), but this controller always includes the suffix for naming clarity.

### Write / Read Data Phase Assignment

The write-data and read-data sub-interfaces also replicate per phase. Two additional parameters control phase placement:

- `WRPHASE` — which phase carries the active write-data beat (default: phase 0)
- `RDPHASE` — which phase carries the active read-data beat (default: phase 0)

These are PHY-vendor-specific in real silicon; we make them parameters so a real-PHY integration can override.

### Idle Phase Drives

The gear output stage drives the per-phase signals to their deselected idle values per DFI v2.1 Table 2 when no command is being issued on that phase. This includes both the inactive phases when a single-phase command is issued, and all phases when the scheduler issues NOP.

### Verification

Reuses the DFI BFM's `DFIPhaseAdapter` (Python) as a reference model — the same gear ratios, the same conventions. The RTL output passes through the adapter and round-trips via the BFM monitor.
