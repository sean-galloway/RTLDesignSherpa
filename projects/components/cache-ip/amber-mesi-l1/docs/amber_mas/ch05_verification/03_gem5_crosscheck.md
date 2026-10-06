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

# gem5 FSM Cross-Check

## Source

The Python reference model and the formal FSM oracles derive from the gem5 Ruby `MESI_Two_Level` SLICC tables, specifically `L1cache.sm`. The enumerated transient states in that file are the source for the `amber_pkg` state encoding and for the control FSM states in `amber_control`.

## Cross-Check Mechanism

1. Extract every stable and transient state from `L1cache.sm`.
2. Map gem5 events to amber signals (CPU request, snoop type, fill response, drain done).
3. Replay a randomized trace through both the gem5-derived Python model and a future cycle-accurate RTL model.
4. Compare state transitions, CRRESP outputs, and next-state writes.

## Scope

The cross-check covers:

- All M/E/S/I stable states.
- Transient states between stable states and pending responses.
- The six IHI0022 snoop types.
- The onyx D2 coherent issue subset (ReadShared, ReadUnique, CleanUnique, MakeUnique, WriteBack, Evict).

MOESI O-state is out of scope for v1.0; the 3-bit encoding reserves a code for it.

---

**Last Updated:** 2026-10-06
