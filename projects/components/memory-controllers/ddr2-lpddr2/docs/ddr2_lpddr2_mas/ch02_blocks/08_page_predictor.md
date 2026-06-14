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

# HAPPY Page Predictor (`page_predictor_fub`)

**Module:** `page_predictor_fub.sv`
**Location:** `rtl/fub/`
**Status:** Skeleton — to be authored during MAS week

> Synthesized only when `PAGE_POLICY == HAPPY_HYBRID`. See HAS §3.2 `page_predictor` for algorithm details (Ghasempour et al. 2015).

## TODO (Week-of-MAS work)

- Interface signal list (inputs/outputs, widths, parameter dependencies)
- Internal state and storage
- FSM diagram (mermaid in `assets/mermaid/`)
- Datapath timing and per-stage flops
- Timing budget on critical paths
- CSR hooks (observability registers driven by this FUB)
- Verification notes (cocotb test plan)
