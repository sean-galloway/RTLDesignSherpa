# Standing up a new flow

The order below is the one that fails earliest. Each step is checkable before
the next becomes possible.

## 1. Register the board, if it is new

Add `boards/<name>.py` with a `BoardSpec`. The fields that matter are `part`,
`jtag_serial`, and -- only when the UART is not on the JTAG FTDI -- `uart_serial`.
Put every board-specific trap in `notes`; that is what `fpga_board.py info`
prints.

```
python3 projects/fpga-systems/bin/fpga_board.py list
python3 projects/fpga-systems/bin/fpga_board.py info --board <name>
```

## 2. Confirm the board is visible before writing any code

```
python3 projects/fpga-systems/bin/uart_link.py        # ports and USB serials
python3 projects/fpga-systems/bin/fpga_board.py ports --board <name>
python3 projects/fpga-systems/bin/fpga_board.py readback
```

If `ports` prints nothing, the problem is the registry's serial or the cabling,
not your code. On a Genesys 2 both cables must be enumerated.

## 3. Create the directory skeleton

Follow `[[flow-layout]]`; it is the authority. The shape is
`<area>/bin/` for sequences and area libraries, and `<area>/build-<name>/` per
bitstream. Use `build-`, not `flows-` -- see Chapter 5.

## 4. Add the area's environment module

`<area>/bin/<area>_env.py`, anchored to the marker as in Chapter 5. Write this
before the first sequence; everything imports it.

## 5. Give the harness an identity register

Pick a probe shape (Chapter 2) and make the FPGA answer it. Prefer a read-only
build-ID constant over a writable scratch register: `register_probe` is safe to
aim at a board running someone else's bitstream and `scratch_probe` is not.

## 6. Write the init sequence first

`<area>/bin/seq_init.py`. Everything else will declare `requires = ("init",)`.
It returns what later steps need -- taps, a profile, a topology.

**Read the build's topology from a register rather than assuming it.** A
single-decoder build once failed every run because the host was faithfully
scoring a checker that was tied off. The host should ask the hardware what it
is, not be told at the command line.

## 7. Write the entry point

`<area>/build-<name>/host/host_<thing>.py`. It parses `argv`, resolves the
board and port, builds the bus, constructs a `SequenceContext`, discovers the
area's `bin/`, and calls `runner.run([...])`. It should be thin.

## 8. Make it run in simulation

This is the step that is easiest to skip and most expensive to add later. Drive
the same host code through a cocotb byte channel with `ctx.board = None`. If a
sequence resolves its own port or needs the board object, it will fail here --
which is the point.

Raise the sim baud (`CLKS_PER_BIT`) to fit the time budget. Do not shrink the
campaign; the shortened version is no longer what runs on the board.

## 9. Lock the board paths

Use the standard `program` recipe so `board_lock.sh` wraps it. A flow that
invokes Vivado directly gets no lock, and nothing will tell it so.

## 10. Record what you programmed

Pass `--identity-json` from any flow whose results are evidence, so the identity
verdict lands beside the bitstream sha256.

## Checklist

- [ ] `fpga_board.py info`, `ports`, `readback` all answer
- [ ] An environment module anchored to the marker, not to a level count
- [ ] An identity register, read-only if possible
- [ ] `seq_init.py` returning what later steps need
- [ ] Sequences touch `ctx.bus` only
- [ ] The same host code runs in sim with `ctx.board = None`
- [ ] Board-touching make targets run under the lock
- [ ] `--identity-json` wherever results are kept
