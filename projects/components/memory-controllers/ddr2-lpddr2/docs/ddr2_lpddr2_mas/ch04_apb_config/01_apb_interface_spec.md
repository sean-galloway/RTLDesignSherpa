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

# APB CSR Slave Protocol

**Status:** Skeleton — to be authored during MAS week


The APB CSR slave is the configuration and observation interface.

## Protocol Compliance

APB3 (`pslverr` supported); APB4 (`pstrb`) optional.

## Behavior

- Two-cycle access (SETUP + ENABLE) per the APB spec
- `pslverr` returns 1 for:
  - Writes to unimplemented schemes in `ADDR_MAP_TUNING.scheme_or`
  - Writes to ranks beyond `NUM_RANKS` (PASR registers, observation registers)
  - Writes to read-only registers
  - Reads from reserved addresses
- All registers are 32-bit; sub-32-bit accesses are aligned to 32-bit boundaries

## CDC

The APB↔MC CDC lives in this FUB. See §1.3 and §2.18 `csr_apb_fub` for the CDC topology.

## TODO

- pslverr decision tree
- APB-side timing diagram
- Sub-32-bit access policy
- CDC implementation detail

