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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Interface Check Signals (AMBA5)

## Purpose

When `--amba5` is enabled, the generated module carries the AXI5-Stream
interface-protection signals of IHI 0051B chapter 5 (`Check_Type =
Odd_Parity_Byte_All`) and checks them at its own ports. This is the
`generate_check_logic()` section of `bin/delta_generator.py`. Names and widths
match `rtl/amba/axis5/*`.

## Parity Rule

Odd parity: a check bit and the bits it covers hold an odd number of ones.
Check bit `[n]` covers bits `[8n+7:8n]`, and the top bit covers a short
remainder (section 5.3). A one-bit check (`TLASTCHK`, `TVALIDCHK`,
`TREADYCHK`, `TWAKEUPCHK`) is the inversion of its signal. Every check bit is
one `rtl/common/dataint_parity` instance with `CHUNKS=1` and `parity_type =
1'b0` (odd), so the spec's per-byte layout holds at any width.

## Implementation

Two generate loops follow the TWAKEUP steering block.

**Per master port (`gen_s_chk[m]`).** The crossbar is the receiver here.

```systemverilog
for (genvar g = 0; g < TDATACHK_W; g++) begin : g_tdatachk
    localparam int LO = 8 * g;
    localparam int PIECE_W = (DATA_WIDTH - LO < 8) ? (DATA_WIDTH - LO) : 8;
    dataint_parity #(.CHUNKS(1), .WIDTH(PIECE_W)) u_par (
        .data_in     (s_axis_tdata[m][LO +: PIECE_W]),
        .parity_in   (s_axis_tdatachk[m][g]),
        .parity_type (1'b0),
        .parity      (w_tdatachk_exp[g]),
        .parity_err  (w_tdatachk_err[g])
    );
end
// ... the same for TSTRB (with --strb-width), TID, TDEST, TUSER; TLAST is 1 bit
assign w_payload_err = s_axis_tvalid[m] && (|w_tdatachk_err || ...);
```

- The payload checks (`TDATACHK`, `TSTRBCHK`, `TLASTCHK`, `TIDCHK`,
  `TDESTCHK`, `TUSERCHK`) are enabled by `TVALID`.
- `TVALIDCHK` and `TWAKEUPCHK` are checked on every cycle out of reset.
- `s_axis_treadychk[m]` is generated: the `parity` output of a 1-bit
  `dataint_parity` over the `s_axis_tready[m]` the crossbar drives.
- Any failure sets `s_parity_error[m]`, a sticky flop that only `aresetn`
  clears.

**Per slave port (`gen_m_chk[s]`).** The crossbar is the transmitter here.

- `m_axis_tvalidchk[s]` and `m_axis_twakeupchk[s]` are generated from the
  `TVALID` / `TWAKEUP` the crossbar drives.
- `m_axis_treadychk[s]` is checked on every cycle out of reset. A failure
  sets the sticky `m_parity_error[s]`.

**Carry.** The payload check bits are not recomputed at the slave port. They
travel through the crossbar mux (see Crossbar Multiplexer) with the same grant
as `TDATA`. While no master is granted they idle at all ones, which is the odd
parity of the all-zero idle payload.

## Design Notes

- Carrying the check bits keeps protection end to end. A beat corrupted
  upstream of the crossbar still fails at the downstream receiver. If the
  crossbar regenerated the check bits from its own mux output, the fault would
  be hidden.
- A failed check does not stall or drop the beat. The fabric's job is to
  report the fault, and the system decides how to respond.
- `TWAKEUPCHK` on the slave port is generated from the OR in the TWAKEUP
  steering block, so it is valid before any grant.

## Verification

`dv/tests/test_delta_axis_flat_2x4_strb_amba5.py` (routing, wakeup and
chk_errors) exercises every row above. A mutation check of the generated RTL
showed the suite failing in each of these cases: even parity instead of odd,
the ingress payload check removed, `TDATACHK` corrupted on the carry path,
and `TREADYCHK` not inverted.
