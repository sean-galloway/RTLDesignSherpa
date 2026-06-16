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

# Multi-Rank Programming

> Per HAS §2.1 (multi-rank as differentiator), HAS §3.3 / §3.4 / §3.6 (architecture). FUB-level detail in MAS §2.9 (bank machine per-rank), §2.11 (refresh round-robin + DARP), §2.13 (per-rank power state), §2.14 (per-rank CS_n drive), §2.16 (cross-rank ODT).

---

## Discovery

Software discovers rank count via the capability vector at 0xFF8:

```c
uint8_t get_num_ranks(void) {
    return (apb_read(0xFF8) >> 8) & 0xF;
}
```

This is the actual synthesized `NUM_RANKS`; software should treat it as the authoritative value rather than assuming a default.

## Per-Rank Mode Register Loads

During init, the controller's microprogram automatically iterates the MRS loads across all ranks. Software just writes MR0..MR3 once, and the init engine handles rank iteration:

```c
apb_write(MR0, mr0_value);   // applied to all ranks during init
apb_write(MR1, mr1_value);
apb_write(MR2, mr2_value);
apb_write(MR3, mr3_value);
```

For per-rank MR variations (rare — most multi-rank systems use identical DRAM parts), software can intercept the init engine sequence:

```c
// Stop after pre-MRS phase
apb_write(CTRL, CTRL_INIT_START);
while (STATUS_INIT_STEP_DBG(apb_read(STATUS)) < INIT_STEP_PRE_MRS);

// Drive MRS to each rank individually via the test access path
// (not currently exposed in v1; this is a hypothetical extension)

// Resume
```

In v1, the simpler model is "all ranks use the same MR values"; per-rank MR override is a v2 feature.

## Per-Rank PASR (LPDDR2)

Already covered in §5.2. Recap:

```c
for (int r = 0; r < num_ranks; r++) {
    apb_write(PASR_BANK_MASK_RANK0 + r*4, mask[r]);
}
```

PASR is **per-rank** because each rank has independent MR16/MR17.

## ODT Rule Selection

The controller's ODT behavior is per HAS §3.6 with three modes; runtime selectable via `RANK_TUNING.odt_rule_or`. See §2.16 for the rule details.

```c
void configure_odt_for_dimm(uint8_t mode) {
    // mode: 0 = build default, 1 = DDR2, 2 = LPDDR2, 3 = OFF (NR=1 only)
    uint32_t v = apb_read(RANK_TUNING);
    v = (v & ~ODT_RULE_OR_MASK) | ODT_RULE_OR(mode);
    apb_write(RANK_TUNING, v);

    apb_write(CTRL, CTRL_CONFIG_APPLY);
    while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED));
    apb_write(CTRL, 0);
}
```

For boards with non-standard impedance budgets, override to a specific rule rather than relying on the build-time default.

## Per-Rank Disable

To disable a rank entirely (e.g., for power testing or to skip a faulty rank):

```c
void disable_rank(uint8_t rank) {
    uint32_t v = apb_read(RANK_TUNING);
    v &= ~(1 << (RANK_ENABLE_MASK_SHIFT + rank));
    apb_write(RANK_TUNING, v);

    apb_write(CTRL, CTRL_CONFIG_APPLY);
    while (!(apb_read(STATUS) & STATUS_CONFIG_SETTLED));
    apb_write(CTRL, 0);
}
```

The scheduler suppresses all commands to disabled ranks. AXI bursts addressing a disabled rank are returned with `SLVERR`.

## Address Mapping for Multi-Rank

The rank field's position in the AXI flat address depends on the scheme:

| Scheme               | Rank field position                        |
|----------------------|--------------------------------------------|
| `ROW_MAJOR`          | High bits, above row                       |
| `BANK_INTERLEAVE`    | High bits, above row                       |
| `XOR_HASH`           | High bits (identity), but bank field hashed |

For interleaved-rank access (where consecutive cache lines round-robin across ranks for max parallelism), this is currently NOT a built-in scheme. v2 may add `RANK_INTERLEAVE` if characterization shows the benefit.

For now, software-managed rank interleaving (e.g., the OS striping memory allocations across rank-aligned regions) is the workaround.

## Refresh Behavior with Multi-Rank

Per HAS §3.4 v0.2 and §2.11:

- REFab dispatches per-rank in round-robin (not all-rank simultaneously)
- REFpb selects (rank, bank) tuples via DARP across the full product set
- Per-rank PASR masks are honored independently
- Per-rank `last_ref_age` counters drive DARP fairness

This means a 4-rank system has 4× the refresh time concentrated, but distributed across the timeline so any single rank only blocks for tRFC per refresh — non-target ranks keep operating.

## Power State Per-Rank

Per §2.13:

- Each rank has its own FSM (ACTIVE / APD / SRF / DPD)
- Channel-wide CSR `CTRL.pwr_req_*` applies to all ranks in v1
- Per-rank auto-APD / SRF triggers based on per-rank idleness (AXI traffic to rank r resets rank r's idle counter)
- v1: software can't request "low-power on rank 1 only"; v2 adds per-rank request

Workloads that consolidate to rank 0 will see ranks 1+ auto-enter low-power without software intervention.

## Per-Rank Observation

Telemetry registers exist per (rank, bank):

```c
uint32_t get_row_hit_rate(uint8_t rank, uint8_t bank) {
    return apb_read(OBS_ROW_HIT_RANK0_BANK0 + (rank * num_banks + bank) * 4);
}
```

At NR=1 NB=8, 8 such registers. At NR=4 NB=8, 32. Software queries `num_ranks` and `num_banks` from the capability vector to know how many to iterate.

## Multi-Rank Bring-Up Checklist

| Step                                                                 | Why                                       |
|----------------------------------------------------------------------|-------------------------------------------|
| Verify `0xFF8.cap_max_ranks` matches expected DIMM rank count        | Build / board mismatch                    |
| Check `0xFF8.cap_pasr` if using LPDDR2                                | Need PASR for LPDDR2 bring-up               |
| Set `ODT_RULE_MULTIRANK` per board impedance design                  | Signal integrity                          |
| Verify per-rank ZQ calibration succeeds during init                   | Each rank's drive impedance               |
| Sweep `OBS_REF_LATENCY_RANK<R>_BANK<N>` across rank workload mix     | Per-rank refresh fairness               |
| Stress-test rank-switching (read alternating ranks)                   | tRTRS / tCS timing                         |
| Verify per-rank auto-APD triggers correctly                           | Power telemetry                            |

## Open Questions / Future Work

- **Per-rank MR override.** v2 feature; some DIMMs have rank-specific tuning (rare).
- **Per-rank CSR power control.** v2 feature; in v1 it's channel-wide.
- **RANK_INTERLEAVE address scheme.** v2; needs characterization to confirm benefit.
- **3DS / LRDIMM logical-rank support.** DDR3+ feature; not in DDR2/LPDDR2 anyway.
