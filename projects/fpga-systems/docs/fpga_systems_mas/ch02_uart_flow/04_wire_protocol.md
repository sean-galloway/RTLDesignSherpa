# The wire protocol

Line-oriented ASCII, one request per line, one reply per line. Deliberately
trivial: it is readable in a terminal, it costs the FPGA almost nothing to
parse, and a human debugging a dead board can type it by hand into `screen`.

## Write

```
host -> board :  "W <addr:08X> <data:08X>\n"
board -> host :  "OK\n"
```

```python
cmd = f"W {addr:08X} {data:08X}\n"
self.ser.write(cmd.encode('ascii'))
response = self.ser.read_until(b'\n', size=10)
return response.strip() == b'OK'
```

`write` returns a bool. Anything that is not exactly `OK` is False, including a
timeout, which arrives as an empty read.

## Read

```
host -> board :  "R <addr:08X>\n"
board -> host :  "0x<value:X>\n"
```

```python
cmd = f"R {addr:08X}\n"
self.ser.write(cmd.encode('ascii'))
response = self.ser.read_until(b'\n', size=20).strip()
if response.startswith(b'0x'):
    return int(response[2:], 16)
return None          # malformed or absent
```

Both fields are fixed-width uppercase hex with no `0x` prefix on the request;
the reply to a read **does** carry `0x`. That asymmetry is in the protocol as
implemented and is what the parser keys on.

## Defaults

| Parameter | Value |
| --- | --- |
| Baud | 115200 (`DEFAULT_BAUD`) |
| Data bits | 8 |
| Parity | none |
| Stop bits | 1 |
| Flow control | none |
| Read timeout | 1.0 s default, 0.4 s while probing |

The baud must match the FPGA's configuration. In simulation it does not: see
the next chapter.

## A read of None is ambiguous, and that is worth knowing

`read()` returns None both for "the board sent something I could not parse" and
for "the board sent nothing". Callers that need to distinguish a dead board from
a bad address must do so at a higher level -- typically by probing a known-good
identity register first, which is exactly what the probes in `02_probes.md` are
for.

Both failure shapes print the offending response, so the distinction is visible
in a log even though it is not in the return value.

## Addressing

Addresses are 32-bit and byte-addressed; a 32-bit register at word index `n`
sits at `base + 4*n`. Host code should not compute these by hand: use the
generated register map for the area and address registers **by name**. See
`vault/handbook/dv/registers-by-name.md` for why offsets written into host code
are a recurring source of silent breakage after an RDL change.
