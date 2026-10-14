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

# System Requirements

## Overview

Everything your system owes the bridge before it will do its job: one clean clock, an asynchronous active-low reset, a single power domain, interfaces that follow the AXI4 rules, and an address map with no overlaps. Gaps in the map are allowed — the bridge answers those addresses itself — and the checklist at the end tells you how to prove all of it.

### Clock Infrastructure

| Requirement | Specification |
|-------------|---------------|
| Clock source | One fabric clock (`aclk`) for the fabric and every master port; a `cdc = true` AXI4 slave port brings its own `<slave>_aclk` (HAS 4.5a) |
| Clock quality | Low jitter, stable frequency |
| Clock distribution | Must reach all Bridge ports |

: Table 6.1: Clock Requirements

### Reset Infrastructure

| Requirement | Specification |
|-------------|---------------|
| Reset type | Asynchronous, active-low (aresetn) |
| Reset synchronization | External synchronizer recommended |
| Reset distribution | Must reach all Bridge ports |

: Table 6.2: Reset Requirements

### Power

| Requirement | Specification |
|-------------|---------------|
| Power domains | Single domain (no power gating) |
| Voltage | FPGA/ASIC process-dependent |

: Table 6.3: Power Requirements

## Parameters

### Address Map

| Requirement | Specification |
|-------------|---------------|
| Slave ranges | Must not overlap |
| Range alignment | Power-of-2 recommended |
| Coverage | Gaps are permitted: an address in no slave range is claimed by the internal subtractive slave and answered with DECERR (see 4.5). It is still a fault -- it is reported, not tolerated. |

: Table 6.4: Address Map Requirements

### Connectivity

| Requirement | Specification |
|-------------|---------------|
| Matrix completeness | All masters must access at least one slave |
| Reachability | Consider traffic patterns for performance |

: Table 6.5: Connectivity Requirements

## Ports

### Master Requirements

Masters connecting to Bridge must:

1. **Comply with AXI4 protocol** - Valid/ready handshake
2. **Use correct ID width** - Match configured ID_WIDTH
3. **Use correct data width** - Match configured DATA_WIDTH
4. **Use correct address width** - Match configured ADDR_WIDTH
5. **Stay within address range** - Target valid slave addresses

### Slave Requirements

Slaves connecting to Bridge must:

1. **Comply with AXI4/APB protocol** - Based on configuration
2. **Accept the widened ID** - a slave sees `{master index, master id}`: the widest master's id_width plus `$clog2(NUM_MASTERS)` bits (none for a single master). Declare the slave's `id_width` at least that wide; the validator refuses less.
3. **Match configured data width** - Or use width conversion
4. **Respond to all transactions** - No hanging

## Timing

### Setup/Hold

| Constraint | Requirement |
|------------|-------------|
| Input setup | Meet FPGA/ASIC requirements |
| Input hold | Meet FPGA/ASIC requirements |
| Clock-to-output | Per process characterization |

: Table 6.6: Timing Requirements

### Recommended Margins

| Margin | Value | Purpose |
|--------|-------|---------|
| Setup margin | 10-20% | Variation tolerance |
| Hold margin | Positive | No hold violations |
| Clock uncertainty | Include in constraints | PLL/MMCM jitter |

: Table 6.7: Recommended Timing Margins

## Testing

### Pre-Integration Checks

1. **RTL lint clean** - No Verilator warnings
2. **Parameter validation** - All parameters in valid range
3. **Address map review** - no overlaps. Complete coverage is NOT required: a
   gap is claimed by the subtractive slave and answered with DECERR (4.5). Decide
   deliberately which you want -- a gap that is meant to be a gap is fine, a gap
   you did not know about is a bug the fabric will now report.
4. **ID width calculation** - Sufficient for NUM_MASTERS

### Integration Checks

1. **Signal connectivity** - All ports connected
2. **Width matching** - DATA_WIDTH, ADDR_WIDTH, ID_WIDTH
3. **Protocol matching** - AXI4 vs APB correctly configured
4. **Clock/reset connectivity** - All ports share same domain

### Post-Integration Checks

1. **Basic transaction test** - Read/write to each slave
2. **Arbitration test** - Multi-master contention
3. **Error handling test** - unmapped-address response: DECERR + 0xDEADBEEF, `unmapped_irq` sticky, `SUBTRACTIVE_STATUS.CLEAR` clears it (see 4.5)
4. **Performance validation** - Meet throughput targets

## Assumptions and Known Limitations

### Response-Ordering Assumption

Bridge routes B and R by a sideband master index stored per slave. For an
AXI4/AXI5 slave of a multi-master bridge (or any slave with `enable_ooo`)
the store is `bridge_cam`, looked up by the returned BID/RID, so the slave
may complete different IDs in any order (ARM IHI 0022E §A4). Every other
slave -- single-master bridges, AXI4-Lite/APB/Wishbone shim slaves and the
internal subtractive slave -- uses an in-order FIFO and must return
responses in request order, which those slaves do by construction.

### Buffer and CAM Depths

All adapter skid depths, response-tracking FIFO depths, and CAM dimensions
are generation-time constants. There is no runtime sizing API. A
systematic sizing rule that relates buffer depth to credit-loop latency,
outstanding-transaction count, and width-converter buffering is tracked
as bridge vault TASK-016.

## References

* ARM, *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022E — AXI4 ordering rules allow out-of-order completion across IDs (§A4). ([Reference archive](../../../references/README.md))
* Maaref, *Architecting and Building High-Speed SoCs*, Packt 2022 — AMBA-suite context and the AXI ID ordering rules that Bridge's FIFO mode simplifies (ch3 §4.2). ([Reference archive](../../../references/README.md))
* Eschemann, *The FPGA Programming Handbook*, Packt 2023 — educational secondary source describing out-of-order reads as a normal AXI4 feature (ch8 §8.3). ([Reference archive](../../../references/README.md))
