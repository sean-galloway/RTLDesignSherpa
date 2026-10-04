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

# Training: Write Leveling Inherited, Read Leveling New

## The family rule: interfaces in hardware, searches in firmware

This family has made the training decision once already, and andesite makes
the same decision for the same reasons. scoria's D2 settled it for write
leveling: the controller provides the *interface* — the DFI handshake, the MR
path, the timing windows, the telemetry — and the *search* runs in firmware.
A delay-line walk's step size, tap count, monotonicity and temperature
behaviour are PHY properties, not controller properties, and a calibration
bug should be a script edit, not a respin.

**Corroborated by LiteDRAM, once again.** The same generated-core check that
backed scoria's D2 backs this extension: LiteDRAM's training support is
enable-plus-strobe registers with no leveling state machine, and its DDR4
generation adds read-leveling and CA-training knobs in exactly that shape. An
independent, deployed controller reaching the same conclusion is worth more
than the argument on its own — and it tells us the interface shape that works
in practice.

So andesite's training blocks obey three rules, inherited:

1. **No search loop in hardware.** Anywhere. The blocks handshake, sequence,
   window, and report; firmware walks.
2. **The four-state telemetry rule.** A host must distinguish never attempted,
   attempted and converged, attempted and timed out, and attempted with no
   result across the whole window — a detector that has never fired is not
   evidence of anything (pumice's data-integrity CRC lesson, quoted in full in
   scoria's book and not repeated here).
3. **Timeout is the controller's to define.** Where a JEDEC window's maximum
   is controller-dependent, the CSR defines it with a distinct status bit —
   a host that waits forever for a result it will never get is
   indistinguishable from a broken link.

## Write leveling: `wrlvl_ifc`, MODIFIED

The interface is scoria's, carried with its contract intact: DFI leveling
handshake, MR1 path in and out of the DRAM's leveling mode, the `tWL*` timing
windows as runtime CSRs, prime-DQ result capture, and the four-state
telemetry. The marking is MODIFIED for one bounded reason: the
training-interface family grows a read-leveling sibling, and the shared
machinery (handshake discipline, window enforcement, telemetry framing) is
factored so both interfaces ride it. What the module owes the host is
unchanged.

## Read leveling: `rdlvl_ifc`, NEW

DDR4's fly-by topology skews DQS against CK on the read side too, and the
DRAM can help: MR3's **MPR** (multi-purpose register) makes the DRAM drive a
known, training- only pattern onto DQ, so the controller can observe its read
capture timing without any memory array in the loop.

| Responsibility | Detail |
|---|---|
| DFI read-leveling handshake | request/acknowledge per chip select with the DFI v4.0 read-training signals `§TBC(TASK-005)` |
| MPR path | MRW into and out of MPR access mode via MR3, sequenced against the handshake |
| Timing windows | the MPR readout and pre/post-pattern intervals as runtime CSRs, named per JESD79-4 |
| Result capture | the training pattern's observed value per chip select, presented to the host |
| Telemetry | the four-state rule above: attempts, results, window, completion |

: Table 3.5: `rdlvl_ifc` responsibilities

The search is firmware's: enable MPR, capture, walk the read delay, cache the
result. The block never decides anything.

## LPDDR4 CA/WDQ training: `ca_train_ifc`, NEW

LPDDR4's bus needs training DDR4 doesn't: the **CA bus itself** must be
trained (LPDDR4 samples CA against CK, and both edges matter), and the
write-DQ path needs its own calibration step. JESD209-4 carries both through
the MPC command's training opcodes — which is why this block sits beside
`zq_ctrl`'s MPC submodule in the dependency graph and reuses the formatter's
LPDDR4 CA path.

| Responsibility | Detail |
|---|---|
| MPC training-opcode issuer | CA training entry/exit and WDQ calibration steps over the 6-bit CA bus |
| DFI training handshake | LPDDR4's training-mode signalling to the PHY, per DFI v4.0 `§TBC(TASK-005)` |
| Timing windows | the JESD209-4 training intervals as runtime CSRs |
| Result capture | the sampled CA/DQ observation per step, presented to the host |
| Telemetry | the four-state rule; per-channel because LPDDR4's channels train independently |

: Table 3.6: `ca_train_ifc` responsibilities

**A scope note.** Whether LPDDR4 CA training is *mandatory before operation*
is board-dependent; the init chapter (3.2) records it as a conditional step.
The interface exists either way — a board that needs it must not require new
hardware to use it.

## What training costs the surrounding blocks

The training interfaces touch three other blocks, and the touches are
bounded. The `init_sequencer` gains training-entry states after ZQ
(firmware-triggered, not autonomous — init hands the bus to training
explicitly). The `mode_register` carries the MR3 MPR fields and the LPDDR4
training-related MRs. The `dfi_cmd_formatter`'s LPDDR4 CA submodule issues
the MPC training opcodes. No datapath block changes for training; the read
and write paths already carry whatever the PHY loops back.
