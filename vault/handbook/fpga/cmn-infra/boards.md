---
title: Boards
summary: The board registry - JTAG serials, UART chips, and the gotchas that eat an afternoon.
---

# Board handling (this lab)

**The registry is the source of truth: `projects/fpga-systems/bin/boards/`.** One file per board,
holding the part, the JTAG serial, and how its UART is reached. Nothing else in
the tree should name a JTAG serial again -- seven copies of `program_fpga.tcl`
each hardcoded one, plus its own env-var name to override it.

```
from boards import get_board
b = get_board("nexys_a7_100t")     # or $FPGA_BOARD
b.find_uart_ports()                 # only THIS board's ports
b.find_uart_port(probe=...)         # ...and which runs the right bitstream
b.program("bitstream/ddr2_char.bit")
```

CLI: `python3 projects/fpga-systems/bin/fpga_board.py {list,info,ports,program}`.

**Flow Makefiles do not call that CLI directly** -- they include the global make
infra (`make/fpga_flow.mk` for the whole flow, or `make/fpga_board.mk` for the
board half alone; see [[build-flows]]), which gives every flow `make program`,
`make ports`, `make board-info` and `make boards`, switchable with
`BOARD=genesys2`. Adding a flow adds no board logic; adding a board adds no flow
logic.

Shared JTAG chain - select by serial (`FPGA_JTAG_SERIAL`; the older per-flow
`RAPIDS_CHAR_JTAG_SERIAL` / `STREAM_CHAR_JTAG_SERIAL` are still honoured, but do
not add more):
- Nexys A7:  210292B7D46F  (xc7a100t)
- Genesys 2: 200300B818A0  (xc7k325t)

## Finding the right port

The USB-UART re-enumerates across reboots and replugs, so the `ttyUSB` index is
never stable and must not be hardcoded. Two filters, and BOTH are needed:

- **USB serial** narrows to one board. On the Nexys A7 the UART and JTAG are
  interfaces of one FT2232, so the JTAG serial identifies the UART too. Match
  loosely: the interface letter ('...D46F' vs '...D46FB') may or may not be
  present on either side, and an exact compare makes a present board read as
  absent.
- **An identity probe** confirms which bitstream is loaded. The serial cannot
  know that; the probe cannot tell two identically-programmed boards apart.

`Board.find_uart_port(probe=...)` applies both. Areas supply the probe (pumice:
`ddr2_char.harness_probe()`, a BUILD_ID read by name).

## Picking the JTAG target: a serial is not enough

A serial identifies a *cable*, not a *scan chain*, and one cable can present
more than one target. On the Genesys 2 Vivado enumerates BOTH FT2232 channels:

```
localhost:3121/xilinx_tcf/Digilent/200300B818A0     <- no scan chain
localhost:3121/xilinx_tcf/Digilent/200300B818A0B    <- xc7k325t_0 lives here
```

Only the `...A0B` one has a device. Opening the other gives

```
ERROR: [Labtools 27-2269] No devices detected on target .../200300B818A0
```

which reads as *board missing* when the board is powered, programmed and fine.

**The registered serial is a PREFIX of the real target name**, so the obvious
selection is quietly wrong:

```tcl
set tgt [lsearch -inline -glob [get_hw_targets] "*$want_serial*"]   ;# WRONG
```

That matches both and returns whichever Vivado listed first -- today, the
chainless one. Every `program_fpga.tcl` in the tree had this line, and it
"worked" only while enumeration order happened to favour the JTAG channel. It
is a latent bug that ordering masked, not a regression: running the old logic
today picks the wrong channel too.

Note the tension with the UART rule above -- loose matching is *required* there
(an exact compare makes a present board read as absent) and *insufficient*
here. Same interface letter, opposite conclusions, because one is choosing a
serial port and the other a scan chain.

**The rule: match by serial, then select the candidate that actually reports a
device.** Implemented once in `projects/fpga-systems/bin/program_fpga.tcl`:

```tcl
set matches [lsearch -all -inline -glob $targets "*$want_serial*"]
# longest name first: the JTAG channel is the more specific one
set matches [lsort -command {...by descending length...} $matches]
foreach cand $matches {
    if {[catch {current_hw_target $cand; open_hw_target}]} {
        catch {close_hw_target}
        catch {disconnect_hw_server}     ;# see poisoning, below
        connect_hw_server
        continue
    }
    if {[llength [get_hw_devices]] > 0} { set tgt $cand; break }
    catch {close_hw_target}
}
```

**A failed open POISONS the session for the sibling channel.** Probe the
chainless target first and the good one then *also* reports "no scan chain" --
which is why a first fix that only added the device check still failed on both.
Reconnecting the hw_server between attempts clears it; trying the longest name
first usually avoids the situation entirely.

Debug this with `get_hw_targets` plus a per-target `get_hw_devices`, never by
trusting the serial. `capture_ila.tcl`-style scripts that grab the first target
have the same exposure.

## Gotchas

- **Genesys 2 UART is a SEPARATE FT232R (serial AU05X8RM)**, not the JTAG
  FT2232 -- matching its UART against the JTAG serial finds nothing, which reads
  as "no board" when the board is right there. Recorded as `uart_serial` in its
  board file so the lookup works. Both cables must be plugged; if the FT232R is
  not enumerated there is no UART, whatever the bitstream does.
- Digilent Adept kills the UART ttyUSB. Do NOT power-cycle the board after
  programming - reprogram loses the port binding.
- ftdi_sio does not block Vivado programming; no driver dance needed.
- A7 note: its stream_char build sits on a timing knife-edge at 100 MHz
  (compressor CAM); the K325T does not - prefer the Genesys for monitor
  work ([[timing-closure]]).

## Related

- [[host-stack]] - what you do once you have the port
- [[sequences]] - the campaign that runs over it
