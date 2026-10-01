# The link and the bridge

Two objects sit between a host program and a register: `UartLink` carries bytes,
`UARTAxiBridge` turns register operations into bytes. They are separate so that
the second can be driven by something other than the first.

## UartLink

A pyserial client that is also a **byte channel**: it satisfies the same
protocol as the simulation-side `SerialChannel` in `bin/TBClasses/harness/`.

| Method | Purpose |
| --- | --- |
| `write(data) -> int` | Send bytes |
| `read_until(expected=b"\n", size=None) -> bytes` | Read to a delimiter |
| `reset_input_buffer()` | Discard buffered input |
| `reset_output_buffer()` | Discard buffered output |
| `close()` | Close the port |
| `is_open` | Property |

Construction opens the port, sleeps a short settle interval, and flushes both
buffers -- a USB-UART that has just been opened will otherwise hand you
fragments of whatever was in flight before.

```python
with UartLink("/dev/ttyUSB3", baudrate=115200) as link:
    bridge = link.bridge()
    bridge.write(0x1_0000, 0xDEADBEEF)
```

`UartLink` is a context manager, and `bridge()` is a convenience for
`open_bridge(channel=self)`.

**pyserial is imported lazily**, inside `__init__` rather than at module scope,
so a machine without it can still import `uart_link` for port enumeration and
for the unit tests. The sim path never touches a real port.

## UARTAxiBridge

Turns 32-bit register reads and writes into the ASCII protocol of the next
chapter.

| Method | Returns |
| --- | --- |
| `write(addr, data)` | True when the board answered `OK` |
| `read(addr)` | The 32-bit value, or None on a malformed reply |
| `write_verify(addr, data)` | True when a readback matches |
| `dump_memory(start, num_words=16)` | List of `(addr, data)` |
| `fill_memory(start, values)` | Writes a list of words |

`addr` and `data` accept an `int` or a hex string (`"0x44A00000"`).

## The injection point

```python
def __init__(self, port='/dev/ttyUSB1', baudrate=115200, timeout=1.0,
             channel=None):
    if channel is not None:
        self.ser = channel
        return
    import serial
    ...
```

When `channel` is given, no serial port is opened and `port`, `baudrate` and
`timeout` are ignored. Anything satisfying the byte-channel protocol works: a
`UartLink`, a cocotb driver, or a tracing wrapper that records the wire for
later comparison.

This single branch is what makes the sim and silicon paths one piece of code.
It is the subject of `05_sim_equivalence.md`.

## Resolving the bridge's location

```python
open_bridge(port=None, baudrate=..., timeout=..., channel=None)
```

`uart_axi_bridge` is a sibling module in the same directory, and `open_bridge`
inserts that directory on `sys.path` before importing it. The bridge used to
live beside the converter RTL it talks to, and every host tool re-derived that
location by hand -- through `$REPO_ROOT`, or a parent walk whose depth broke the
moment the layer moved. There is no path derivation left to get wrong here; see
Chapter 5 for the general rule.
