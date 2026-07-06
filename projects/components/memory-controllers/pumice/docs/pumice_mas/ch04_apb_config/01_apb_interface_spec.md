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

# APB CSR Slave Protocol

> Per HAS §2.4 §3 for the per-signal port list and HAS §4.3 for the architectural view. This chapter is the **wire-level contract** for the APB CSR slave specific to this controller.
>
> The CSR is implemented entirely inside `csr_apb_fub`. The CDC topology is documented in MAS §1.3 and the CKE/quiet-point coordination is in §2.13.

---

## Compliance Profile

| Aspect                          | Support level                                              |
|---------------------------------|------------------------------------------------------------|
| APB3 (ARM IHI 0024B)             | Full — `psel`, `penable`, `pwrite`, `paddr`, `pwdata`, `pready`, `prdata`, `pslverr` |
| APB4 `pstrb` (byte enables)      | Optional, `SUPPORT_APB_PSTRB = false` default              |
| APB4 `pprot`                     | Not supported                                              |

## Address Space

The slave decodes a 4 KB region (12-bit `paddr`). All registers are 32-bit, naturally aligned on 4-byte boundaries.

| Address range  | Region                                |
|----------------|---------------------------------------|
| 0x000 – 0x00F  | Control + Status                       |
| 0x010 – 0x01F  | Timing parameters                     |
| 0x020 – 0x02F  | Mode Register values                  |
| 0x030 – 0x03F  | LPDDR2-specific (PASR, temperature)   |
| 0x040 – 0x04F  | Scheduler / Refresh / Page tuning     |
| 0x050         | Init tuning                           |
| 0x080 – 0x0FF  | Per-(rank, bank) observation          |
| 0x100 – 0x1FF  | System observation / telemetry        |
| 0xFF0 – 0xFFC  | Module identification + capability    |

Detailed register map is in §4.2; the full bit-level layout is in HAS §6.3.

## Behavior

### Access Cycles

Standard APB3:

```
SETUP:   psel=1, penable=0   → slave samples paddr/pwdata/pwrite
ENABLE:  psel=1, penable=1   → slave returns pready + prdata + pslverr
IDLE:    psel=0              → no transaction
```

`pready` is asserted in the ENABLE phase. The slave does not insert wait states in v1 — all transactions complete in 2 cycles.

### Sub-32-Bit Accesses

All registers are 32-bit. The slave does not support sub-word access:

- APB3 (without `pstrb`): all 32 bits are read or written
- APB4 with `pstrb`: when `SUPPORT_APB_PSTRB = true`, byte-strobe is honored; `pstrb = 0` returns `pslverr`

### Error Conditions

The slave asserts `pslverr` (in the ENABLE phase) for:

| Condition                                                                 | Notes                                            |
|---------------------------------------------------------------------------|--------------------------------------------------|
| Read from reserved address (gaps in the address space)                    | Returns `pslverr`; prdata is 0                    |
| Write to read-only register                                                | Returns `pslverr`; register unchanged             |
| Write to ranks beyond `NUM_RANKS` (PASR / observation)                    | Returns `pslverr`                                 |
| Write to unsupported address-map scheme (per HAS §6.3 ADDR_MAP_TUNING)    | Returns `pslverr`                                 |
| Write to ODT_RULE_OR with un-synthesized rule                              | Returns `pslverr`                                 |
| Init not done, write to traffic-blocking control bit                      | Honored normally — software may want to pre-load   |

## CDC Topology

The APB slave is the **only** FUB in the `apb_pclk` domain. The CDC into the controller's `mc_clk` domain happens inside `csr_apb_fub` per MAS §1.3:

- Write side: per-field 4-flop synchronizer with edge-detect strobe into the MC-side staging register
- Read side: per-counter pulse-sync + Gray code

The CDC is transparent to APB software; reads and writes complete in the standard 2-cycle APB access.

## Runtime Override Semantics

Runtime override fields commit at the next quiet point (see §4.3). Software sequence:

1. Write the new value to the staging field via APB (returns immediately)
2. Write `CTRL.config_apply = 1` to request immediate commit (or skip and wait for natural quiet point)
3. Poll `STATUS.config_settled`
4. The new value is now live in the MC-side datapath

See §4.3 for full sequencing detail.

## Performance

| Operation                | Latency             |
|--------------------------|---------------------|
| Single APB read           | 2 PCLK cycles        |
| Single APB write          | 2 PCLK cycles        |
| Read with CDC counter sync| 2 PCLK cycles (sync transparent — the MC-side counter is sampled at APB read time) |
| Write + immediate commit  | 2 PCLK + < 256 MC cycles drain to quiet point |
| Continuous read polling   | One transaction every 2 PCLK cycles (50 MHz PCLK → 25 M transactions/s) |

## Open Questions / Future Work

- **APB4 `pprot` support.** Some SoCs use it for security tagging. Add as `SUPPORT_APB_PPROT` parameter if needed.
- **Burst reads.** Multiple consecutive `paddr` reads currently take 2 PCLK each. Some APB masters support fast-path burst reads. Punt unless software flags it.
- **CDC-bypass for fast register access.** When `apb_pclk == mc_clk`, the CDC adds unnecessary latency. A `BYPASS_CDC` parameter could detect same-domain operation. Punt.
