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

# monbus_record_expander

**Module:** `monbus_record_expander.sv`
**Location:** `rtl/amba/ocelus/`
**Status:** New (2026-10-23); the raw expander of `monbus_group_core`, lifted out

**Plane:** output plane

---

## Overview

`monbus_record_expander` turns one MonBus record (128-bit packet plus 64-bit source timestamp) into the three 64-bit beats of the raw memory layout and pushes them, atomically, into a beat-granular FIFO:

| Beat | Contents |
|---|---|
| 0 | `{tag[3:0] = 4'h0, source_ts[59:0]}` |
| 1 | `packet[127:64]` |
| 2 | `packet[63:0]` |

: Raw record layout

Once beat 0 is accepted the expander commits to beats 1 and 2, holding `out_valid` until each is taken, so a record is never split across backpressure. `in_ready` is the beat-0 handshake: the upstream record is consumed exactly when its first beat enters the FIFO. Per-beat `out_ready` is used rather than a "three slots free" precheck, which keeps the FIFO count, `wr_valid` and count from closing a combinational loop.

This is the expander `monbus_group_core` carries inline (unchanged there), lifted out so `monbus_group_core_1wr` can run one per source: the error path and the trace path.

---

## Ports

| Port | Dir | Width | Description |
|------|-----|-------|-------------|
| `axi_aclk`, `axi_aresetn` | in | 1 | Clock, active-low async reset |
| `in_valid` | in | 1 | A record is offered; the caller qualifies this with its routing decision |
| `in_ready` | out | 1 | Record consumed (beat 0 accepted this cycle) |
| `in_packet` | in | 128 | `monitor_packet_t` |
| `in_source_ts` | in | 64 | `monbus_timestamp_t`; bits 63:60 are not carried |
| `out_valid` | out | 1 | Beat offered to the FIFO |
| `out_ready` | in | 1 | FIFO not full |
| `out_data` | out | 64 | Beat |

: Ports

---

## Behaviour

Three states, `EXP_TS`, `EXP_HI`, `EXP_LO`: idle in `EXP_TS` offering beat 0 whenever `in_valid`; on its acceptance latch the packet and walk `EXP_HI`, `EXP_LO` back to `EXP_TS`, each step on `out_ready`. One record per three accepted beats; a new record is not looked at until the previous one's last beat is in the FIFO. This is the control path of a 3-to-1 serialiser, not a per-beat datapath machine: the beats are a fixed sequence over one latched value.

---

## Verification

Exercised end to end by `val/amba/test_monbus_group_core_1wr.py` (both instances) and, as the inline copy, by `formal/amba/monbus_group_core`, whose harness models this expander beat for beat. Lint: `make -C rtl/amba verilator-monbus_record_expander`.

---

## Related

- [monbus_group_core](monbus_group_core.md): the inline original
- [monbus_group_core_1wr](monbus_group_core_1wr.md): two instances, one per window
- `rtl/amba/filelists/monbus_record_expander.f`
