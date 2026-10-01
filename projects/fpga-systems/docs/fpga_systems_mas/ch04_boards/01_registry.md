# The board registry

`boards/` holds one file per board. It is the source of truth for the facts host
tooling needs, and it exists because those facts were previously spread across
seven copies of a Tcl script, each with its own hardcoded serial and its own
environment variable to override it.

## BoardSpec

```python
@dataclass
class BoardSpec:
    name: str                              # registry key
    display_name: str
    part: str                              # xc7a100tcsg324-1
    jtag_serial: Optional[str] = None      # Vivado hw_target serial
    uart_serial: Optional[str] = None      # only when UART != JTAG FTDI
    uart_baud: int = DEFAULT_BAUD
    uart_glob: str = "/dev/ttyUSB*"
    notes: Sequence[str] = field(default_factory=tuple)
```

`jtag_serial` pins JTAG when several Digilent boards share a chain and -- when
`uart_serial` is None -- doubles as the USB serial of the UART, because both
interfaces are on one FTDI part. `uart_serial` exists for boards where that is
not true.

`notes` is not decoration. It carries the board-specific traps that cost an
afternoon, and it is printed by `fpga_board.py info`.

## The two boards in this lab

| | Nexys A7-100T | Genesys 2 |
| --- | --- | --- |
| Part | `xc7a100tcsg324-1` | `xc7k325tffg900-2` |
| JTAG serial | `210292BFA3EE` | `200300B818A0` |
| UART | Same FT2232HQ as JTAG | **Separate FT232R**, serial `AU05X8RM` |
| `uart_serial` | None | `AU05X8RM` |

They share a JTAG chain, which is why the serial and not the board name is what
distinguishes them.

Recorded traps, from the specs themselves:

- **Nexys A7:** Digilent Adept steals the UART ttyUSB; do not power-cycle after
  programming or the port binding is lost. `ftdi_sio` does not block Vivado
  programming -- no driver dance is needed.
- **Nexys A7:** the lab has had two A7-100T units on this desk. If `make ports`
  reports nothing, check `udevadm info /dev/ttyUSB*` -- a swapped unit presents
  as exactly that symptom.
- **Genesys 2:** both the FT232R and the JTAG FT2232 must be enumerated or there
  is no UART, whatever the bitstream does.

## Using it

```python
from boards import get_board

b = get_board("nexys_a7_100t")        # or $FPGA_BOARD, else the default
b.find_uart_ports()                   # only THIS board's ports
port = b.find_uart_port(probe=my_probe)
b.program("bitstream/ddr2_char.bit")
```

Subclass `Board` only when a board needs different behaviour; most need only a
`BoardSpec`. `boards/genesys2.py` is a subclass because of its split UART.

## The CLI

```
fpga_board.py list                       # known boards
fpga_board.py info    --board genesys2   # the spec, including notes
fpga_board.py ports   --board genesys2   # this board's UART ports
fpga_board.py serial  --board genesys2   # the JTAG serial, for Tcl
fpga_board.py readback                   # what is on the JTAG chain
fpga_board.py program --bitstream x.bit
```

`serial` prints nothing and exits 0 when the board has no serial, so a caller
can substitute it unconditionally and get "any target" rather than the literal
string `None` used as a match pattern.
