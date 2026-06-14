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

# Error Handling

**Status:** Skeleton — to be authored during MAS week


Error reporting paths and the software response model.

## TODO

- Error categories: init failure, refresh-deadline miss, AXI queue overflow, DFI rddata-valid timeout
- IRQ topology (`irq_init_done`, `irq_init_error`, `irq_overflow`)
- Clearing latched errors via CSR
- Diagnosis sequence: history register (`STATUS_HISTORY`), debug observation FUBs
- Software recovery patterns (re-init, soft-reset, full reset)

