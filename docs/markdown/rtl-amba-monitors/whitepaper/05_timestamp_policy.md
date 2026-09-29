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

# Timestamp policy

A 64-bit timestamp rides beside every packet (`monbus_timestamp_t`). Today
it is the monbus group family's local free-running counter (`mon_time_out`),
distributed to the wrappers as `i_mon_time`, and the group writes its low 60
bits into the first beat of every three-beat record. Within one group every
packet is on one clock; across groups there is no shared time base.

Two directions are open to the integrator:

- **Hybrid** `{global_us[47:0], local_cyc[15:0]}`: a system-wide
  microsecond count in the upper bits, the wrapper's own cycle count in the
  lower. Cross-subsystem correlation and per-wrapper cycle resolution then
  share the one field, and nothing in the packet layout moves.
- **External time source** (PTP or a chip-level counter): drive `i_mon_time`
  from it instead of the group's counter. The wrappers do not care where the
  value comes from.

Neither is prototyped; the hybrid form is the one this paper recommends
when it is, because it needs no new field and no host-side re-basing.

![Timestamp policy: the group's local counter today, the hybrid time base as the tweak](../../assets/rtl-amba/monitor_wp_timestamp.png)
