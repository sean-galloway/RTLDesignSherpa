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

# Document Information

## Bridge Generator Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Bridge Generator Architecture Specification |
| Version | 1.2 |
| Date | 2026-10-16 |
| Status | Released |
| Classification | Open Source - MIT License |

: Document information

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-10-12 | RTL Design Sherpa | Initial GAS release — generator code paths verified against `bridge_generator.py`, `bridge_pkg/config.py`, `bridge_pkg/config_validator.py`, `bridge_pkg/config_loader.py`, and emitted artifacts in `rtl/generated/bridge_mix_e/`. |
| 1.1 (renumbered) | 2026-10-15 | RTL Design Sherpa | The bridge document set (GAS, HAS, MAS) is renumbered to one common rev, 1.1; rows above keep the numbers they were published under. Content: the one-target-per-master limitation is fixed (GitHub #119 L1) -- per-ID target tracking (`[bridge].id_track_bits`), B/R response arbiters per master width path, the crossed-W hold; the generated TB carries its connectivity map and the generator emits the AXIL narrow-to-wide alignment test (GitHub #119 L8); per-port outstanding limits, `max_outstanding` (power of two 2..64, default 16), size every tracker -- the fixed 16 removed (GitHub #119 L5); per-port `latency` modes (`cut_all` / `cut_ax` / `cut_none`) and honoured TOML skid depths (GitHub #119 L7); read-return-atomic and trace-echo ports no longer limited to one target (GitHub #119 L1b). |
| 1.2 | 2026-10-16 | RTL Design Sherpa | Slave-adapter CAM pipelining (GitHub #119): `bridge_cam` gains `PIPELINE_ALLOC` (registered insert with a pending-entry bypass; the full flag counts the pending entry) and `PIPELINE_FREE` (registered free; lookups see the post-free state), both on in every CAM-tracked slave adapter -- MAS Figure 4.2. HAS 5.1 adds the Genesys 2 fabric-benchmark results against the Xilinx AXI Crossbar and SmartConnect; HAS 5.3 / 6.4 reference synthesis tables re-measured on the current generator. CDC on master ports (GitHub #119 L2): `cdc = true` on an AXI4 master puts `axi4_cdc_{wr,rd}` between the port and its timing wrapper, with `<master>_aclk` / `<master>_aresetn` on the top (HAS 4.5a, MAS 6.1); new fixture `bridge_3x2_rw_mcdc` and `test_bridge_3x2_rw_mcdc_ratio`. Generated TBs build their protocol checkers after reset. Read width converters are built with `R_INTERLEAVE = 0` (no reassembly pool; it had grown every converter fixture past synthesis), so a slave may not interleave R beats across IDs (HAS 4.1, PRD FR-9). |

: Revision history

## Document Purpose

This Generator Architecture Specification (GAS) is the manual for the Bridge **code generator**. It is written for the engineer who must:

- re-run the generator after a bugfix,
- add a new protocol or port option,
- debug a generated module,
- or audit why a particular file was emitted.

It covers the full generator surface: CLI flags, TOML keys, Python data classes, validation rules, emission stages, output files, and the extension points that are safe to touch.

For the hardware that the generator produces, see the **Bridge HAS** and **Bridge MAS**. For product requirements, see **PRD.md**.

## Intended Audience

- RTL engineers modifying or extending the generator
- Verification engineers regenerating fixtures after a generator change
- System architects adding new bridge configurations to the batch
- Integrators debugging a generated bridge top

## Related Documents

- **Bridge HAS** - Hardware Architecture Specification
- **Bridge MAS** - Micro-Architecture Specification
- **PRD.md** - Product requirements and overview
- **CLAUDE.md** - AI development guide and subsystem rules
