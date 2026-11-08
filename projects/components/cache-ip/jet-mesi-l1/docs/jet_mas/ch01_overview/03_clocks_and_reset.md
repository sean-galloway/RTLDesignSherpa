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

# Clocks and Reset

jet is a single-clock IP, inherited from amber: the CPU-side GAXI port, the
lookup/commit pipeline, the MSHR file, the writeback buffer, the fabric
engines, and the snoop responder all run on `clk`. No CDC paths exist inside
`jet_top`; house AXI/ACE wrappers handle external clock crossing if the
fabric runs elsewhere.

## Reset rules

- `jet_top` / `jet_ace_top` run the `aresetn` pin through the house
  `reset_sync` (N=3, `ASYNC_REG`, `REPLICATED_OUT=1`) before any internal
  block sees it, as amber does; the release the core sees is synchronous,
  N+1 = 4 cycles after the pin. `REPLICATED_OUT` adds the one output flop
  the FPGA tools may replicate: the synchronizer's output is a single net on
  every async-reset flop's CLR pin, and on the Genesys2 that net (about 24k
  endpoints) was jet's worst setup path once the payload stores were RAMs
  (handbook `design/reset-and-clocking.md`, 2026-11-07).
- All **control** flops use `ALWAYS_FF_RST` (active-low async assert), per
  GLOBAL_REQUIREMENTS Category 1.1; `reset_n` inside, `aresetn` at the AMBA
  pins.
- **Payload stores carry no reset** (GLOBAL_REQUIREMENTS 1.4): the tag and
  data arrays, the WB buffer's line words (`jet_wb_buffer.r_data`), the
  response sequencer's word ring (`jet_rsp_seq.r_data`) and the
  `DATA_SYNC_READ` read-data registers. Each is qualified by a reset valid
  bit or pointer, so an unreset word is never observable; under the reset
  macro none of them could be a RAM and each would be one more pin on the
  reset net above.
- **The MSHR valid bits and WB-buffer valid bits reset to empty.** Unlike
  the tag/data arrays (whose contents are undefined until written, with
  invalid state emerging from the uninitialized tag encodings per amber),
  the jet bookkeeping structures must come up empty — a stale valid MSHR
  entry after reset would alias a pending fill that never was.
- The response sequencer resets to "next expected tag = first".
- After reset deassertion the lookup stage is idle and all arrays are
  treated as invalid, as in amber.

## Quiescence

`busy` = lookup/commit non-idle OR any MSHR entry valid OR any WB entry
valid OR any adapter skid occupied. A testbench or power sequencer may only
declare the cache quiescent when `busy` is low — which implies all fills
committed and all drains BRESP-retired (the book's rule that writes must
complete before quiescence is declared, Chinnakonda §10.11, applied at
jet's scale: no barrier instructions exist at this interface, so `busy` is
the whole completion contract).
