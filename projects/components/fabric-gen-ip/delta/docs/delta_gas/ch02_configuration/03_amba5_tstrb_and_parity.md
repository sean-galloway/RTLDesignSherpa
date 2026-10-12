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

# AMBA 5, TSTRB, and Parity Options

## TSTRB byte qualifiers

By default Delta omits `TSTRB` to match the common AXI-Stream use case where every byte is valid. To emit byte-qualifier ports:

```bash
python3 delta_generator.py --masters 2 --slaves 4 --strb-width 8
```

The generator adds `s_axis_tstrb` and `m_axis_tstrb` arrays and muxes them alongside `TDATA`.

## AMBA 5 sidebands (`--amba5`)

When `--amba5` is set, the generator adds `TWAKEUP` and the full AXI5-Stream
interface-protection set of IHI 0051B chapter 5, `Check_Type =
Odd_Parity_Byte_All`. It also adds a sticky error flag on every port. The
signal names and widths match `rtl/amba/axis5/*`, so a generated crossbar
connects directly to those modules.

`--amba5` needs a whole-byte `--data-width`, because `TDATACHK` has one bit
per `TDATA` byte. The CLI rejects anything else.

| Check signal | Width (Table 5-1) | Width parameter | Covers |
|---|---|---|---|
| `TDATACHK` | `DATA_WIDTH/8` | `TDATACHK_W` | `TDATA` |
| `TSTRBCHK` | `ceil(STRB_WIDTH/8)` (only with `--strb-width`) | `TSTRBCHK_W` | `TSTRB` |
| `TLASTCHK` | 1 | -- | `TLAST` |
| `TIDCHK` | `ceil(ID_WIDTH/8)` | `TIDCHK_W` | `TID` |
| `TDESTCHK` | `ceil(DEST_WIDTH/8)` | `TDESTCHK_W` | `TDEST` |
| `TUSERCHK` | `ceil(USER_WIDTH/8)` | `TUSERCHK_W` | `TUSER` |
| `TVALIDCHK` | 1 | -- | `TVALID` |
| `TREADYCHK` | 1 | -- | `TREADY` |
| `TWAKEUPCHK` | 1 | -- | `TWAKEUP` |

: AMBA 5 check signals emitted by `--amba5`

Each width parameter is derived in the generated module header, for example
`parameter int TDATACHK_W = DATA_WIDTH / 8`. If you override a payload width
at instantiation, the check ports follow it. There is no separate parity-width
option, because the spec fixes the widths. The old `--parity-width` flag has
been removed.

### Parity rule

Odd parity: a check bit and the bits it covers always hold an odd number of
ones. Check bit `[n]` covers bits `[8n+7:8n]`. When a signal is not a whole
number of bytes, the top check bit covers the short remainder (IHI 0051B
section 5.3). A one-bit check is the inversion of its signal. The crossbar
computes and checks every bit with one `rtl/common/dataint_parity`
instance (`CHUNKS=1`, `parity_type=0`). The generated file therefore needs
`dataint_parity` in its compile closure: `-f
$REPO_ROOT/rtl/common/filelists/dataint_parity.f`, as
`rtl_test/filelists/delta_axis_flat_2x4_strb_amba5.f` does.

### Who generates and who checks

| Port side | Signal | Crossbar action |
|---|---|---|
| master (`s_axis_*`), crossbar receives | payload `*CHK` | Checked against the payload while `TVALID` is high. Then carried to the granted slave port unchanged, by the same grant mux as `TDATA`. |
| master | `TVALIDCHK`, `TWAKEUPCHK` | Checked every cycle out of reset (check enable is `ARESETn`). |
| master | `TREADYCHK` | Generated from the `TREADY` the crossbar drives. |
| slave (`m_axis_*`), crossbar transmits | payload `*CHK` | Carried from the granted master. When no master is granted, they idle at all ones, the odd parity of the all-zero idle payload. |
| slave | `TVALIDCHK`, `TWAKEUPCHK` | Generated from the `TVALID` / `TWAKEUP` the crossbar drives. |
| slave | `TREADYCHK` | Checked every cycle out of reset. |

: Check-signal ownership per port

The payload check bits are carried, not regenerated. A check bit that arrives
bad at a master port therefore reaches the slave still bad, and both the
crossbar and the downstream receiver can see it.

### Error flags

`s_parity_error[NUM_MASTERS]` and `m_parity_error[NUM_SLAVES]` are sticky and
are cleared only by `aresetn`. A master port's flag sets on a bad payload
`*CHK` beat, a bad `TVALIDCHK`, or a bad `TWAKEUPCHK`. A slave port's flag
sets on a bad `TREADYCHK`. The crossbar does not drop or alter a beat that
fails its check. The flag reports the failure and the beat is still delivered.

### TWAKEUP steering

`TWAKEUP` is treated as a hint that may arrive before `TVALID`. The generator decodes it directly from `TDEST` without waiting for a grant:

```systemverilog
m_axis_twakeup[s] = OR over all m of (s_axis_twakeup[m] && s_axis_tdest[m] == s);
```

`m_axis_twakeupchk[s]` is generated from this OR.
