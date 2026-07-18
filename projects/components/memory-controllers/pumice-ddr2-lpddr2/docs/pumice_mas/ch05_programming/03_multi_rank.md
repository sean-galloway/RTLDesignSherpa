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

> Per HAS §2.1 (multi-rank as differentiator), HAS §3.3 / §3.4 / §3.6 (architecture). FUB-level detail in MAS §2 (`pumice_bank_timers` per (rank,bank), `refresh_ctrl` round-robin, `dfi_cmd_formatter` CS_n / ODT).
>
> Note: the default board build is single-rank (`NUM_RANKS = 1`). This chapter documents the intended multi-rank programming model; the single-rank RDL declares only `*_RANK0` registers, and per-rank register generation is a follow-up (see §4.2).

---

## Discovery

There is no capability vector register in this build. Software knows `NUM_RANKS` from the build parameter (it is a synthesis-time geometry parameter, see §6.1); the `ID` register (0xFF0) reports memtype and phase count but not rank count. Treat the build parameter as authoritative.

## Per-Rank Mode Register Loads

During init, the sequencer (intended multi-rank extension) iterates the MRS/MRW loads across ranks. Software writes MR0..MR3 once:

```c
csr_write(MR0, mr0_value);   // applied to all ranks during init
csr_write(MR1, mr1_value);
csr_write(MR2, mr2_value);
csr_write(MR3, mr3_value);
```

For DDR2 the sequencer uses its own JEDEC-correct MR words; the `MR*` CSRs are the software-visible shadow (see §5.1). Per-rank MR variation (rare) is a future feature.

## Per-Rank PASR (LPDDR2)

Already covered in §5.2. In the single-rank build:

```c
csr_write(PASR_BANK_MASK_RANK0, mask);
```

A multi-rank build adds `PASR_BANK_MASK_RANK{N}` registers (each rank has independent MR16/MR17).

## ODT

ODT is handled inside `dfi_cmd_formatter` / `mode_register` (there is no standalone ODT control block and no `RANK_TUNING.odt_rule_or` CSR). `dfi_odt_o` is driven per command. Board-specific ODT rule selection is not a runtime CSR knob in this build; it is baked into the formatter's per-command ODT logic. For boards with non-standard impedance budgets, adjust the formatter's ODT policy at build time.

## Per-Rank Disable

There is no `RANK_TUNING` rank-enable CSR in this build. Rank enable/disable is a multi-rank feature to be added alongside per-rank register generation. In the single-rank build there is one rank and it is always active.

## Address Mapping for Multi-Rank

The rank field always sits in the high bits of the (byte-offset-stripped) word address, above the row — its position is invariant. The single `ADDR_MAP.bank_lsb` knob only slides the **bank** field within the column region (see §4.4 and `rtl/fub/addr_mapper.sv`); the rank field is unaffected by `bank_lsb`. The `hash_en` XOR-hash folds row bits into the bank index only — it does not touch the rank field.

There is no rank-interleave mode. Software-managed rank interleaving (the OS striping allocations across rank-aligned regions) is the workaround if consecutive-line rank striping is desired.

## Refresh Behavior with Multi-Rank

Per HAS §3.4 and MAS §2 (`refresh_ctrl`, intended multi-rank extension):

- REFab dispatches per-rank in round-robin (not all-rank simultaneously)
- REFpb (LPDDR2) selects (rank, bank) tuples via the `REFRESH_TUNING.refpb_policy_or` policy
- Per-rank PASR masks are honored independently

A multi-rank system distributes refresh across the timeline so any single rank only blocks for tRFC per refresh — non-target ranks keep operating.

## Power State Per-Rank

- Channel-wide CSR `CTRL.pwr_req_*` applies to all ranks (there is no per-rank power request CSR)
- `STATUS.power_state[7:4]` reports the encoded state
- Per-rank auto-low-power is not a CSR feature in this build (there is no `POWER_TUNING`; see §5.2)

## Per-Rank / Per-Bank Observation

The RDL declares per-bank observation arrays for rank 0: `OBS_ROW_HIT[8]` (0x080..0x09C) and `OBS_REF_LATENCY[8]` (0x0C0..0x0DC). The generated regmap flattens them to indexed names:

```c
uint32_t get_row_hit(uint8_t bank) {
    return csr_read(OBS_ROW_HIT0_ROW_HIT + bank * 4);   // read-clear
}
```

A multi-rank build adds the per-rank arrays. (Note: `hwif_in` observation readback is tied off in `pumice_top` today — see §4.1.)

## Multi-Rank Bring-Up Checklist

| Step                                                                 | Why                                       |
|----------------------------------------------------------------------|-------------------------------------------|
| Verify the build's `NUM_RANKS` matches the expected DIMM rank count  | Build / board mismatch                    |
| Program `PASR_*_RANK{N}` if using LPDDR2                              | PASR for LPDDR2 bring-up                   |
| Verify per-rank ZQ calibration succeeds during init                   | Each rank's drive impedance               |
| Sweep `OBS_REF_LATENCY[bank]` across rank workload mix               | Per-rank refresh fairness                 |
| Stress-test rank-switching (read alternating ranks)                   | tRTRS / tCS timing                        |

## Open Questions / Future Work

- **Per-rank register generation.** The RDL declares only `*_RANK0`; a `NUM_RANKS` loop is needed for PASR/temp/observation and rank-enable.
- **Per-rank MR override.** Some DIMMs have rank-specific tuning (rare).
- **Per-rank power control.** `CTRL.pwr_req_*` is channel-wide; per-rank request registers are a follow-up.
- **Runtime ODT rule select.** ODT is currently baked into `dfi_cmd_formatter`; a runtime CSR knob could be reintroduced if board diversity needs it.
