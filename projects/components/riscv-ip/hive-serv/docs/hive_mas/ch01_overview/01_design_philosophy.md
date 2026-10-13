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

# Design Philosophy and Machine Organization

## Philosophy

HIVE's micro-architecture follows three rules, in priority order:

1. **Hierarchy mirrors control.** Every block's structure reflects the
   control hierarchy: one `hive_c_controller` at the top, sixteen identical
   `serv_monitor` instances below it, one `control_network` binding them,
   one `config_manager` orchestrating the fabric they all touch. A reader
   should be able to draw the HAS block diagram from the RTL tree alone.

2. **Reuse the repo's fabric.** Clock crossing uses `rtl/cdc/` primitives;
   AXIS buffering uses the repo GAXI FIFO/skid library; arbitration uses the
   repo round-robin arbiter. HIVE's own RTL is only what is genuinely new:
   descriptor generation, monitor glue, control framing, context switching.

3. **Observability is a feature, not a debug afterthought.** Every block
   exposes the signals the Ocelus monitor system (see `rtl/amba/ocelus/`)
   and the cocotb testbenches need, on dedicated observation ports that are
   part of the module interface — never tapped ad hoc from internals.

## Machine Organization

```
hive_top                              # top-level integration
├── hive_c_controller/                # Block 1
├── serv_monitor/        (16×)        # Block 2
├── control_network/                  # Block 3
├── config_manager/                   # Block 4
└── common/                           # shared utilities (or repo imports)
```

Block details are specified in Chapter 2. The four clock domains and their
crossings are specified in the next section of this chapter; CDC structure
constrains several block interfaces, so it comes first.

## What Is Imported vs. What Is Built

| Item | Source | Why |
|------|--------|-----|
| HIVE-C CPU | VexRiscv (SpinalHDL, generated) | RV32IM 5-stage core; not reinvented |
| SERV monitor CPU | SERV (olofk, RTL) | Bit-serial RV32I; smallest monitor that can run real trigger logic |
| AXIS async FIFOs | repo GAXI / `rtl/common` | Gray-pointer CDC, already verified |
| Reset synchronizers | `rtl/cdc/` | Async-assert/sync-deassert, house style |
| Descriptors, taps, triggers, framing, contexts | **HIVE RTL (new)** | The actual product of this component |

: Imported vs. built

---

**Last Updated:** 2026-10-12
