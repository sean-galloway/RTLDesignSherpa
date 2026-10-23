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

# The Generated rapids-g Tree

**Generator:** `bin/gen_rapids_g.py`
**Status:** Implemented (rapids TASK-034)
**Last Updated:** 2026-10-21

---

Above `scheduler_g` the rapids-g RTL is RAPIDS's, so it is derived rather than copied:

| Generated | From | Edits |
|---|---|---|
| `rtl/macro_g/generated/scheduler_group_array_g.sv` | `rtl/macro/scheduler_group_array.sv` | rename; `scheduler` becomes `scheduler_g`; the `seq_*` ports wired; `scheduler_group_array_g_seq.svh` (one `rapids_seq_g`) included in front of the scheduler loop; `$fatal` unless `SHARED_ENGINES` = 1 and `NUM_CHANNELS` is 4, 8 or 16 |
| `rtl/macro_g/generated/rapids_src_g.sv`, `rapids_snk_g.sv` | `rtl/macro/rapids_src.sv`, `rapids_snk.sv` | rename; the array becomes `scheduler_group_array_g` |
| `rtl/macro_g/generated/rapids_core_g.sv` | `rtl/macro/rapids_core.sv` | rename; the halves become `_g` |
| `rtl/top_g/generated/rapids_g_top_base.sv` | `rtl/top/rapids_top_base.sv` | rename; the core becomes `rapids_core_g`; `apb4_slave`'s cmd/rsp outputs renamed `host_*`; `rapids_g_top_reg_arb.svh` (host + both gatlings into the register command queue) included after it |
| `rtl/top_g/generated/rapids_g_top.sv`, `rapids_g_cxs_top.sv` | the -g base | the thin-top derivation of `bin/gen_plane_tops.py` |
| `rtl/top_g/generated/rapids_g_16ch_top.sv`, `rapids_g_16ch_cxs_top.sv` | the -g base | the same, `NUM_CHANNELS` = 16; compiled with `rtl/filelists/top_g/rapids_g_16ch{,_cxs}_top.f`, which select the 16-channel register map (rapids TASK-036) |

: Table 5.4.1: Generated files

The register-mailbox master (`seq_reg_*`) is added to every level's port list after `rst_n` and connected at every instance (array -> half -> core as `src_` / `snk_` -> top base), so the RAPIDS files need no knowledge of it.

Every edit matches its anchor exactly once or the generator fails, so a RAPIDS change that moves an anchor is a failed run, not a wrong file. `python3 bin/gen_rapids_g.py --check` exits 1 when any generated file is stale. The filelists are `rtl/filelists/fub_g/`, `macro_g/` and `top_g/`; they pull gatling through `$GATLING_ROOT/rtl/filelists/top/gatling_core.f`, and the 8-channel register map as `top/rapids_top_base.f` does.
