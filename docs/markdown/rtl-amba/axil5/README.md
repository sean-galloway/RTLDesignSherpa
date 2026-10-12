<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# AXI5-Lite (AXIL5) Modules

**Location:** `rtl/amba/axil5/`
**Sibling family:** [AXI4-Lite](../axil4/README.md)

---

## Overview

Sixteen modules mirroring the AXI4-Lite family one for one, with the AXI5-Lite optional signal groups threaded through. Same channel set, same handshakes, same single-beat semantics -- what AXI5-Lite adds is sideband.

If you came here looking for a full AXI5-Lite protocol stack, read the next section before you instantiate anything.

---

## Functional Description

These modules **transport** AXI5-Lite signals. They do not execute AXI5-Lite semantics:

- MPAM, MECID, NSAID, LOOP and TRACE are carried end to end unmodified. Nothing here interprets a partition ID or an encryption context.
- POISON is carried. It is never generated and never checked.
- LOCK is carried with no exclusive-access monitor behind it. A completer returning EXOKAY is not validated against anything.

Those behaviours belong to the endpoints on either side. Read this before treating the family as a full AXI5-Lite protocol stack -- it is not one.

AXI4-Lite vs AXI5-Lite, as this library implements them:

| Feature | AXI4-Lite | AXI5-Lite |
|---|---|---|
| Channels | AW, W, B, AR, R | same |
| Burst support | none | none |
| Transaction ID | none | none |
| User sideband | not present | `AxUSER`/`WUSER`/`BUSER`/`RUSER`, gated by `ENABLE_USER` |
| Trace | not present | `AxTRACE`/`BTRACE`/`RTRACE`, gated by `ENABLE_TRACE` |
| Loopback ID | not present | `AxLOOP`/`BLOOP`/`RLOOP`, gated by `ENABLE_LOOP` |
| MPAM / MECID / NSAID | not present | on the address channels, each independently gated |
| Poison | not present | `WPOISON`/`RPOISON`, one bit per 64 data bits |
| Exclusive access | not present | `AxLOCK`, gated by `ENABLE_LOCK` |

**With every group disabled the two are the same interface.** The packed payload widths match channel for channel, which is what lets one testbench bind to either family.

---

## Usage Example

Two configurations of the same module -- every group off, and the security qualifiers on:

```systemverilog
// AXI4-Lite-equivalent: every group off, payload widths identical to axil4
axil5_master_rd #(
    .AXIL_ADDR_WIDTH (32),
    .AXIL_DATA_WIDTH (32),
    .ENABLE_USER (0), .ENABLE_TRACE (0), .ENABLE_LOOP  (0), .ENABLE_MPAM (0),
    .ENABLE_MECID(0), .ENABLE_NSAID(0), .ENABLE_POISON(0), .ENABLE_LOCK (0)
) u_plain ( /* ... */ );

// With the security qualifiers, which is what AXI5-Lite is usually for
axil5_master_rd #(
    .AXIL_ADDR_WIDTH (32),
    .AXIL_DATA_WIDTH (32),
    .NSAID_WIDTH (4), .MPAM_WIDTH (11), .MECID_WIDTH (16),
    .ENABLE_NSAID(1), .ENABLE_MPAM(1), .ENABLE_MECID(1),
    .ENABLE_USER (0), .ENABLE_TRACE(0), .ENABLE_LOOP (0),
    .ENABLE_POISON(0), .ENABLE_LOCK(0)
) u_secure ( /* ... */ );
```

---

## Design Notes

Known limitations:

- No protocol checking of the optional groups. The monitored variants observe handshakes, addresses, responses and timing; `axi_monitor_filtered` has no ports for MPAM, MECID, NSAID, TRACE, LOOP or POISON.
- No exclusive-access monitor. `AxLOCK` is transported; nothing tracks exclusive state or validates EXOKAY.
- No poison generation or checking.
- Timing diagrams are not yet drawn for this family.

---

## Related Modules

The family, grouped by what each variant adds:

### Transport (4)

| Module | Channels |
|---|---|
| [axil5_master_rd](axil5_master_rd.md) | AR, R |
| [axil5_master_wr](axil5_master_wr.md) | AW, W, B |
| [axil5_slave_rd](axil5_slave_rd.md) | AR, R |
| [axil5_slave_wr](axil5_slave_wr.md) | AW, W, B |

### Clock-gated (4)

| Module | Adds |
|---|---|
| [axil5_master_rd_cg](axil5_master_rd_cg.md) | One `amba_clock_gate_ctrl` over the whole inner module |
| [axil5_master_wr_cg](axil5_master_wr_cg.md) | One `amba_clock_gate_ctrl` over the whole inner module |
| [axil5_slave_rd_cg](axil5_slave_rd_cg.md) | One `amba_clock_gate_ctrl` over the whole inner module |
| [axil5_slave_wr_cg](axil5_slave_wr_cg.md) | One `amba_clock_gate_ctrl` over the whole inner module |

### Monitored (4)

| Module | Adds |
|---|---|
| [axil5_master_rd_mon](axil5_master_rd_mon.md) | `axi_monitor_filtered`, monbus packet output |
| [axil5_master_wr_mon](axil5_master_wr_mon.md) | `axi_monitor_filtered`, monbus packet output |
| [axil5_slave_rd_mon](axil5_slave_rd_mon.md) | `axi_monitor_filtered`, monbus packet output |
| [axil5_slave_wr_mon](axil5_slave_wr_mon.md) | `axi_monitor_filtered`, monbus packet output |

### Monitored and clock-gated (4)

| Module | Adds |
|---|---|
| [axil5_master_rd_mon_cg](axil5_master_rd_mon_cg.md) | Both, with ready held low while gated |
| [axil5_master_wr_mon_cg](axil5_master_wr_mon_cg.md) | Both, with ready held low while gated |
| [axil5_slave_rd_mon_cg](axil5_slave_rd_mon_cg.md) | Both, with ready held low while gated |
| [axil5_slave_wr_mon_cg](axil5_slave_wr_mon_cg.md) | Both, with ready held low while gated |

---

## Testing

`val/amba/test_axil5_*.py` -- sixteen runners, 42 parameterised cases, all passing. They drive the modules with **every optional group enabled**, which makes them the only tests in the repo that exercise the AXI5-Lite sideband against real transport RTL rather than a behavioural model.

The testbench classes in `bin/TBClasses/axil5/` are the AXI4-Lite ones with the component factories swapped and the group widths set in `COMPONENT_KWARGS`. One definition of the traffic and its checks.

Also here: `test_axil5_opt_signals.py` drives `axil5_opt_slave`, a behavioural slave under `rtl/amba/axil5/test-modules/` built purely so the BFMs had a DUT carrying every optional port. It is test collateral -- do not instantiate it in a design.

## References

- Arm. *AMBA AXI Protocol Specification*, ARM IHI 0022, Issue L, Aug. 2025. [developer.arm.com/documentation/ihi0022/l](https://developer.arm.com/documentation/ihi0022/l) -- §B2.1.5 "AXI5-Lite" and Table B2.2 signal matrix; carried groups per §A12.5 User defined signaling, §A12.3 Trace signals, §A12.4 User Loopback signaling, §A12.1 MPAM, §A4.6 Memory Encryption Contexts, §A10.1 NSAID, §A16.1 Poison; handshake on the AR/R and AW/W/B channels per §A2.3.1/§A2.3.2; register stages per §A2.5. Table B2.2 marks AxLOCK, AxMPAM, AxMECID, AxNSAID and AxLOOP not present on AXI5-Lite and AxID mandatory on a Subordinate: this module carries the former as `ENABLE_*` extensions and has no ID ports (in-order subset).
- Arm. *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022, Issue H, 2020. [developer.arm.com/documentation/ihi0022/h](https://developer.arm.com/documentation/ihi0022/h) -- Part C ch. C2 "AMBA AXI5-Lite", §C2.2 comparison with AXI4-Lite and §C2.5/§C2.6 upgrading an AXI4-Lite master/slave: the every-group-disabled build is the AXI4-Lite-equivalent port.
- Cortadella, J., Kishinevsky, M., Grundmann, B. "Synthesis of Synchronous Elastic Architectures." *Proc. 43rd Design Automation Conf. (DAC '06)*, pp. 657-662, 2006. DOI: [10.1145/1146909.1147077](https://doi.org/10.1145/1146909.1147077) -- the elastic buffer; its Property 3.1 (capacity C >= 2 for full throughput) is the depth-2 floor of each channel's `gaxi_skid_buffer`.
- Carloni, L.P., McMillan, K.L., Sangiovanni-Vincentelli, A.L. "Theory of Latency-Insensitive Design." *IEEE Trans. Computer-Aided Design of Integrated Circuits and Systems*, 20(9), Sept. 2001. DOI: [10.1109/43.945302](https://doi.org/10.1109/43.945302) -- relay stations: storage on a back-pressured channel adds latency without changing function.
- Benini, L., Bogliolo, A., De Micheli, G. "A Survey of Design Techniques for System-Level Dynamic Power Management." *IEEE Trans. VLSI Systems*, 8(3), June 2000. DOI: [10.1109/92.845896](https://doi.org/10.1109/92.845896) -- fixed-timeout shutdown: gate after `cfg_cg_idle_count` idle cycles, wake on any VALID.
- Benini, L., De Micheli, G. "Automatic Synthesis of Low-Power Gated-Clock Finite-State Machines." *IEEE Trans. CAD*, 15(6), June 1996. DOI: [10.1109/43.503933](https://doi.org/10.1109/43.503933) -- the latch-based glitch-free clock gate under `clock_gate_ctrl`.
- Chipressian. *Crack the Hardware Interview -- from RTL Designers' Perspective: Architecture and Micro-architecture Design*, ch. 2 "Handshake Protocols", Q8 valid-ready protocol and Q9 valid-ready slices -- textbook treatment of register slices (secondary source).
- Bruno, F., Eschemann, G. *The FPGA Programming Handbook*, 2nd ed., Packt, 2024, ch. 8 "Introduction to AXI", §8.3 "AXI4 interfaces (full and AXI-Lite)" -- textbook treatment of the AXI-Lite channel set (secondary source).
- Roy, S. *Advanced Digital System Design*, Springer, 2024, ch. 15 "Low-Power Digital System Design", §15.5.5 "Logic Level Power Down" -- textbook treatment of disabling the clock to idle units (secondary source).
- Indexed in `rtl/amba/references/README.md` (local PDF: `ElasticBuffer__Cortadella2006.pdf`); clock-gating papers in `rtl/common/references/` (local PDF: `DynamicPowerManagementTimeout__Benini2000.pdf`, `LatchBasedClockGating__Benini1996.pdf`)

---

## Navigation

[AMBA overview](../overview.md) | [AXI4-Lite](../axil4/README.md) | [AXI5](../axi5/README.md)
