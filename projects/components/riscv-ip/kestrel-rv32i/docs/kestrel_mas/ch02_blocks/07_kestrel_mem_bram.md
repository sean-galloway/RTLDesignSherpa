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

# kestrel_mem_bram

## Purpose

`kestrel_mem_bram` is the block-RAM alternative to `kestrel_mem_loader`
(owner, 2026-10-20): a board-sized memory with **registered reads** behind
the same core ports and the same AXIL address map. A single-cycle core cannot
wait for a synchronous read on its own, so the wrapper holds it with
`mem_wait` while a read lands. Every instruction takes two clocks and a load
three; the ISA is untouched (HAS Ch. 4, memory contract property 2).

| | `kestrel_mem_loader` | `kestrel_mem_bram` |
|---|---|---|
| Storage | 2 x 64 KB distributed RAM | 1 x 128 KB block RAM, true dual port |
| Core reads | combinational | registered, core held with `mem_wait` |
| CPI | 1 (2 for a cross-word access) | 2, 3 for a load (plus the retry beat) |
| Word index | byte-address bits [13:0] (aliases, see Ch. 2.6) | `addr[16:2]`, no aliasing |
| Run control | sticky `run` | `run` writable both ways: 0 returns to load mode |
| Status | `run` | halted, cause, cycles, instret, last gp write |

: Loader and block-RAM wrapper compared

## The Array

One `logic [31:0] r_mem [32768]` with `ram_style = "block"`, written per byte
lane and read through an output register on each port (the inference
template Vivado maps to RAMB36 in true-dual-port mode; 32 tiles). Port A
serves the core, port B the AXIL loader. Code, data and `.tohost` share one
address space, as in every other kestrel memory (fetch and L/S coherent, so
`rv32ui-p-fence_i` runs).

## The Sequencer (Port A)

Three states, one register of instruction word:

| State | Port A | `mem_wait` | Leaves to |
|---|---|---|---|
| FETCH | read at `imem_addr` (the PC) | 1 | EXEC |
| EXEC | `imem_rdata` = the read; present `dmem_addr`; a store writes at the end of the cycle | 1 for a load, else 0 | LOAD for a load, else FETCH |
| LOAD | hold; `dmem_rdata` = the read, `imem_rdata` = the captured word | 0 | FETCH |

: The fetch / execute / load sequencer

The instruction word is captured at the end of EXEC so it stays valid through
LOAD, where the same port's output now holds the load data. A store commits
in EXEC, the cycle the core retires it, so the next FETCH already sees it. A
cross-word access is two core cycles (HAS Ch. 4 retry), each going round the
sequencer. While the core is in load mode the sequencer parks in FETCH.

## AXIL Side (Port B)

The write side is the loader's: the `axil4_slave_wr` leaf, an AW holding
register and a B holding bit. Memory writes are accepted only in load mode.
The read side takes two stages, because port B's read is registered: AR is
accepted into a wait cycle, the array (or register) data is copied into a
holding register, and R is offered from there and held under backpressure.
AR is refused in a cycle where a loader write owns port B.

## Registers (`addr[17] = 1`)

| `addr[4:2]` | Name | Access |
|---|---|---|
| 0 | CTRL/STATUS | W bit 0 `run` (1 releases the core, 0 returns to load mode); R `{cause[7:4], halted[1], run[0]}` |
| 1 | CYCLES | clocks since `run` was set, frozen at halt |
| 2 | INSTRET | retired instructions (RVFI beats) |
| 3 | GP | last value written to x3 -- the riscv-tests verdict, since kestrel halts on the final ecall before the `tohost` store |
| 4 | BUILD_ID | `0x4B42524D` ("KBRM") |

: kestrel_mem_bram registers

Setting `run` from 0 clears halted, cause and the counters.

## Verification

- `dv/tests/test_kestrel_mem_bram.py`: the rv32ui battery through this path
  with the golden-interpreter diff and spike lockstep (42/42 at func), the
  registers (status, counters, CPI 2..3, stop / reload / rerun) and AXIL
  backpressure on the two-stage read. A wrapper mutant (no instruction hold
  through LOAD) fails 12 of the 42 images.
- `formal/kestrel/riscv-formal`: every check with `mem_wait` driven freely;
  a core mutant (register write not gated by `mem_wait`) fails `reg` in one
  second.
- On the Genesys 2: `projects/fpga-systems/Genesys2/riscv-ip/kestrel`, the
  same host programs over UART in sim and on the board.
