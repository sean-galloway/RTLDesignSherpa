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

# AXI3 Integration

## Boundary-Conversion Architecture

The bridge crossbar is AXI4 internally. An AXI3 port is therefore converted at
the boundary, not natively carried through the fabric:

- **AXI3 slave port** (`protocol = "axi3"` on a slave): the crossbar's AXI4
  master face drives `axi4_to_axi3`, whose AXI3 master face presents the
  external slave pins.
- **AXI3 master port** (`protocol = "axi3"` on a master): the external AXI3
  master drives `axi3_to_axi4`, whose AXI4 slave face feeds the ordinary AXI4
  master timing wrapper and the rest of the adapter.

Both converters require the AXI3 data width and the paired AXI4 width to match;
any width adaptation is the bridge's internal `dwidth_converter` or
`axil_to_axi4_wide_align` path *behind* the protocol converter, exactly as it
is for native AXI4 ports.

## Converter-Sourced Constraints

The bridge does not enforce AXI3 semantics itself — it instantiates the
converters and relies on their contracts. The constraints below are taken from
the converters MAS:

1. **No write-data interleaving across IDs.** `axi4_to_axi3_wr` stamps every
   AXI3 W beat with the current AWID and does not support interleaved W IDs;
   `axi3_to_axi4_wr` accepts only one outstanding write transaction at a time
   and asserts `ASSERT_A3_WID_STABLE` if `WID` changes mid-burst or differs
   from the active AWID. The upstream AXI3 master must keep W beats in
   transaction order.
2. **Egress bursts longer than 16 beats are chopped.** `axi4_to_axi3_rd` and
   `axi4_to_axi3_wr` split AXI4 bursts into sequential AXI3 bursts of up to 16
   beats each; `INCR` and `FIXED` bursts are advanced/regenerated, while
   `WRAP` bursts longer than 16 beats are deferred (assertion-rejected).
3. **QoS and REGION are absent on AXI3 pins.** `axi4_to_axi3` drops them;
   `axi3_to_axi4` drives them to zero.
4. **Same-width converters only.** `AXI_DATA_WIDTH` must be identical on both
   sides; the bridge places its existing width-adaptation logic behind the
   converter when the external AXI3 width differs from a target slave width.
5. **Lock mapping per the ARM AXI3 encoding** (ARM IHI 0022: `00` normal,
   `01` exclusive, `10` locked), as fixed by bridge GitHub #98:
   - `axi4_to_axi3`: `1'b0 → 2'b00`, `1'b1 → 2'b01`.
   - `axi3_to_axi4`: `2'b01 → 1'b1`; `2'b00`, `2'b10` (locked — AXI4 dropped
     locked accesses), and the reserved `2'b11` → `1'b0`.

6. **Bandwidth (measured, HAS 5.1).** An AXI3 master has one write in
   flight (W7, from item 1), so its writes run at beats / (beats + ~8)
   beats per cycle: 0.674 at 16 beats, 0.111 single-beat. Its reads are not
   limited. An AXI3 slave (W8) takes one AR or AW at most every other cycle
   and one transaction per ID at a time, and loses a W cycle per AXI3
   burst. With eight IDs in flight, reads reach 0.50 single-beat and 1.000
   at two beats or more.
7. **AXI3 slaves do not synthesize yet (W10, HAS 5.1).** `axi4_to_axi3_rd`
   and `axi4_to_axi3_wr` use SystemVerilog queues, which Vivado rejects. A
   bridge with an AXI3 slave simulates and passes its regression, but no
   FPGA build of it is possible until the converter's queues are replaced
   with FIFOs.

See converters MAS §3.15 *AXI4 to AXI3 Converter*
([`15_axi4_to_axi3.md`](../../../../../../components/utility-ip/converters/docs/converter_mas/ch03_protocol_blocks/15_axi4_to_axi3.md))
and §3.16 *AXI3 to AXI4 Converter*
([`16_axi3_to_axi4.md`](../../../../../../components/utility-ip/converters/docs/converter_mas/ch03_protocol_blocks/16_axi3_to_axi4.md))
for the full contracts.

## Validation Evidence

The following generated configurations exercise AXI3 on both boundaries and
pass the bridge GATE and FUNC regression suites:

- `bridge_1x2_axi3`
- `bridge_2x2_axi3_masters`
- `bridge_2x2_axi3_slaves`
- `bridge_mix_e`

### Configuration constraints

The bridge validator enforces these AXI3-specific rules at configuration time:

- AXI3 port data widths must be one of {32, 64, 128, 256}.
- CDC on an AXI3 port is rejected in this version.
- AXI3 masters require `id_width > 0`.
- AXI3 slave `id_width` must be at least the fabric's master-index-prefixed
  width (the same rule that applies to AXI4 slaves).

## References

* ARM, *AMBA 3 AXI Protocol Specification*, ARM IHI 0022 — the AXI3 protocol
  authority; 4-bit `AxLEN`, 2-bit `AxLOCK`, write-data `WID`, absence of
  `QoS`/`REGION`. ([Reference archive](../../../references/README.md))
* ARM, *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022E — the AXI4
  protocol authority. ([Reference archive](../../../references/README.md))
