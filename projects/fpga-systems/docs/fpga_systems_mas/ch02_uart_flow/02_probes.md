# Probes

Narrowing by USB serial says which ports belong to a board. It does not say
which of them is the one the harness is listening on, nor whether the board is
running the bitstream you think it is. A probe answers that.

```python
Probe = Callable[[UartLink], bool]
```

A probe is handed an **open** link and returns True or False. It must not raise
on a wrong-but-healthy board -- returning False is enough, because the loop is
going to try the next candidate either way.

The probe stays a caller concern because each harness identifies itself
differently. Two shapes occur in this repository, and both ship.

## register_probe -- read-only

```python
register_probe(addr=0x1_0000, magic=0x44445232)
```

Reads one register and compares it to an identity constant. Used by the rapids
(`CSR_ID`), cdc (`BUILD_ID`) and pumice (`BUILD_ID`) harnesses.

**Read-only, so it is safe to aim at a board running someone else's bitstream.**
Prefer this shape when you have the choice.

## scratch_probe -- round-trips a scratch register

```python
scratch_probe(addr=0x1_0004, magic=0xC0FFEE5A)
```

For harnesses whose identity register is a plain scratchpad rather than a
build-ID constant. Used by the stream characterization harness.

**This one WRITES, and that makes it dangerous in a way the other is not.**
Every harness in this lab speaks the same ASCII protocol, so a write lands
wherever `addr` points in *that* board's map. It does not bounce off a board
that is not yours.

Two mitigations are built in, and neither removes the need to narrow candidates
first:

- The original value is read before the write and **restored on a mismatch**, so
  a probe that hits someone else's board does not abandon a magic number in one
  of its registers.
- On a match the scratch is zeroed, which is its resting state.

Narrow the candidate set before probing -- `Board.find_uart_port(probe=...)`
filters by USB serial first -- rather than scanning every `ttyUSB` on the host.

## The resolution order

```python
find_port(probe=None, want=None, candidates=None, baudrate=..., timeout=0.4,
          label="harness", pattern="/dev/ttyUSB*", verbose=True) -> str
```

1. An explicit `want` (the caller's `--port`) is tried **first but still
   probed**. A stale path in a script therefore fails loudly instead of quietly
   driving the wrong board. The string `"auto"` means "no preference".
2. Then every remaining candidate, in order.
3. The first that answers wins.

A `probe` of `None` means "take the first port that opens", which is only
sensible when exactly one board is attached.

When nothing answers, `find_port` raises `SystemExit` carrying the candidate
list and the question worth asking:

```
[autodetect] no <label> responded on any of: ['/dev/ttyUSB0', '/dev/ttyUSB3'].
Is the board powered and programmed with the right bitstream?
```

`SystemExit` rather than an exception because every caller of this is a CLI, and
a traceback helps nobody.
