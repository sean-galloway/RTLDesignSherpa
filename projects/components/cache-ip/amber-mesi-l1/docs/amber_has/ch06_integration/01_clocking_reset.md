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

# Clocking and Reset

## Clock domain

amber is a single-clock IP. The CPU-side GAXI port, the cache core, the fabric masters, and the snoop adapter all run on `aclk`. There are no CDC paths inside `amber_core`; the house AXI/ACE wrappers handle any external CDC if the fabric runs at a different frequency.

## Reset

All flops use the `ALWAYS_FF_RST` macro with active-low asynchronous assertion, per `GLOBAL_REQUIREMENTS.md` Category 1.1. The reset signal inside project components is `rst_n`; AMBA-facing pins use `aresetn`. Memory arrays (`sdpram_core`-based tag/data stores) have no reset port; their contents are initialized by software or by the first misses after reset.

## Reset sequence

After reset deassertion, `amber_control` starts in the idle state. The tag and data arrays contain undefined values until the first accesses fill them. The front end accepts no request until the control FSM is idle and ready. There is no explicit cache invalidation hardware; invalidation is the natural state of unaccessed lines because the MESI state field is not reset and the first access to any set treats a mismatching/invalid tag as a miss.

## Clock gating

The ACE master and snoop adapter modules expose `busy` outputs. These can be used by the top-level clock-gating cell to shut off the fabric-side clock when the cache is quiescent. The core's `busy` signal is `amber_control`'s non-idle state OR the pending-fill bypass register valid bit OR any skid-buffer occupancy in the adapters.
