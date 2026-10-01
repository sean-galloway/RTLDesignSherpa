# Sim and silicon equivalence

The property this layer is arranged to protect: **the same host code runs
against the FPGA and against a simulation, and the bytes on the wire are
identical.**

## The mechanism

One branch, in `UARTAxiBridge.__init__`:

```python
if channel is not None:
    self.ser = channel
    return
import serial
self.ser = serial.Serial(port, baudrate, timeout=timeout)
```

On silicon the channel is a `UartLink` wrapping a `/dev/ttyUSB*`. In simulation
it is a cocotb UART driver attached to the DUT's RX and TX pins. The protocol
code above that branch does not know which it has, because nothing above the
branch can tell.

Three channel implementations are in use:

| Channel | Where |
| --- | --- |
| `UartLink` | Silicon, over pyserial |
| cocotb UART channel | Simulation, driving the DUT pins |
| `TracingChannel` | Either, wrapping another channel and recording the wire |

`TracingChannel` is what turns "should be identical" into something checkable:
run the same host program both ways, compare the recorded byte streams.

## What differs, and what must not

| Differs | Must not differ |
| --- | --- |
| Baud divider (`CLKS_PER_BIT`) | The byte stream |
| Wall-clock duration | The register addresses touched |
| Presence of a board | The order of operations |
| `ctx.board` (a `Board`, or None) | The host code path |

The baud divider is the interesting one. `rs_loop_top.sv` derives the board
value from the system clock:

```systemverilog
localparam int UART_CLKS_PER_BIT = (CFG_SYS_CLK_HZ + CFG_UART_BAUD / 2) / CFG_UART_BAUD;
```

which at 100 MHz and 115200 baud is about 868 clocks per bit. The simulation
testbench sets `CLKS_PER_BIT = 4`. Same bytes, two orders of magnitude less
simulated time.

## The constraint that follows

A sim-harness test is bounded in simulated time -- in this tree, 100 ms. UART
traffic at a realistic divider blows that budget immediately, which creates a
standing temptation: shorten the campaign so it fits.

**That is the wrong lever.** Shrinking the campaign changes what is under test,
and the shortened version is no longer the thing that runs on the board. Raising
the sim baud changes only how fast the identical byte stream is carried.

The reed-solomon harness states this at the point of temptation, in the test
that would otherwise be shortened:

```python
CLKS_PER_BIT = 4
# ... if the campaign does not fit, the lever is the sim baud
# (CLKS_PER_BIT above), not the parameters and not the campaign.
```

## The anti-pattern

A testbench that builds its own private bridge -- speaking the protocol directly
to the DUT rather than running the host program -- is not an equivalence test.
It is a second implementation, and it will agree with the first right up until
it matters.

The handbook note `[[uart-harness]]` documents this failure and the flows it has
been found in. The rule in Chapter 3 (a sequence never opens its own port) is
what keeps the host side substitutable in the first place.
