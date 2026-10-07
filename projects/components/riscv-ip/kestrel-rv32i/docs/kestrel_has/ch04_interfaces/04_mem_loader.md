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

# kestrel_mem_loader and the AXIL Programming Interface

## Purpose

`kestrel_mem_loader` (`rtl/fub/kestrel_mem_loader.sv`) is the board glue: it wraps the core with two 64 KB on-chip memories (imem, dmem), an AXIL4 slave for image loading, and a run-control register that sequences load-then-run. It composes the repo's skid-buffered AXIL leaf slaves (`axil4_slave_wr`, `axil4_slave_rd`) exactly as `rtl/amba/shared/sdpram_slave_axil_axil.sv` does. Mutual exclusion between the loader and the core is by protocol — there is no contention arbiter and no FSM in the datapath.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `AXIL_ADDR_WIDTH` | int | 18 | AXIL address width; bits [17:0] of the map below |
| `AXIL_DATA_WIDTH` | int | 32 | AXIL data width (one 32-bit word per beat) |
| `MEM_WORDS` | int | 16384 | Words per region: 64 KB imem + 64 KB dmem |
| `SKID_DEPTH_AW` / `SKID_DEPTH_W` / `SKID_DEPTH_B` | int | 2 / 2 / 2 | Write-channel skid depths in the `axil4_slave_wr` leaf |
| `SKID_DEPTH_AR` / `SKID_DEPTH_R` | int | 2 / 4 | Read-channel skid depths in the `axil4_slave_rd` leaf |

: Loader parameters

## AXIL Slave Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `aclk` | Input | 1 | Clock; one clock domain for the whole loader + core |
| `aresetn` | Input | 1 | Active-low reset (load mode re-enters on reset) |
| `s_axil_awaddr` | Input | 18 | Write address (see map) |
| `s_axil_awprot` | Input | 3 | Write protection (ignored) |
| `s_axil_awvalid` / `s_axil_awready` | Input / Output | 1 / 1 | Write address handshake |
| `s_axil_wdata` | Input | 32 | Write data |
| `s_axil_wstrb` | Input | 4 | Byte strobes — honored per byte on loader writes |
| `s_axil_wvalid` / `s_axil_wready` | Input / Output | 1 / 1 | Write data handshake |
| `s_axil_bresp` | Output | 2 | Write response — always `OKAY` (2'b00) |
| `s_axil_bvalid` / `s_axil_bready` | Output / Input | 1 / 1 | Write response handshake |
| `s_axil_araddr` | Input | 18 | Read address (see map) |
| `s_axil_arprot` | Input | 3 | Read protection (ignored) |
| `s_axil_arvalid` / `s_axil_arready` | Input / Output | 1 / 1 | Read address handshake |
| `s_axil_rdata` | Output | 32 | Read data — memory word, or CTRL (`run_q`) readback |
| `s_axil_rresp` | Output | 2 | Read response — always `OKAY` (2'b00) |
| `s_axil_rvalid` / `s_axil_rready` | Output / Input | 1 / 1 | Read data handshake |

: AXIL slave interface

## Core-Side Ports and Debug Taps

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `imem_addr` / `imem_rdata` | Input / Output | 32 / 32 | Core fetch port into the loader's unified map |
| `dmem_req` / `dmem_addr` / `dmem_rdata` / `dmem_wstrb` / `dmem_wdata` | Input / Input / Output / Input / Input | 1 / 32 / 32 / 4 / 32 | Core data port into the loader's unified map; stores merge per byte like the TB store port |
| `core_rst_n` | Output | 1 | Core reset: low in load mode (core held), high once `CTRL.run` is written |
| `o_dbg_busy_wr` / `o_dbg_busy_rd` | Output | 1 / 1 | Leaf-slave busy taps (debug observability; used by the backpressure scenario ML-08) |

: Core-side and debug ports

## Address Map

Byte address bits [17:0]. The array word index is the byte address's low 14 bits, `addr[13:0]`, on every port (AXIL and core) — one convention, so an AXIL write and a core access at the same byte address always touch the same word.

| Address bits | Meaning |
|--------------|---------|
| `addr[17] = 1` | CTRL register; a write with `wstrb[0] & wdata[0]` sets `run` (sticky until reset). Read returns `{31'b0, run}`. CTRL occupies `0x0002_0000` |
| `addr[17] = 0`, `addr[16] = 0` | imem array selected; `addr[13:0]` is the word index |
| `addr[17] = 0`, `addr[16] = 1` | dmem array selected; `addr[13:0]` is the word index |

: Loader address map (AXIL byte addresses)

Address-map properties an integrator must know:

- **Unified array select.** Every port — AXIL and both core ports — selects imem vs dmem by address bit 16, so the core's fetch port can read the dmem array and its data port can reach either array. A flat image (code, `.tohost`, and `.data` interleaved by address, as the riscv-tests p-environment links it) behaves like the unified memory of the simulation testbench.
- **Word indexing.** A word image streams at byte addresses `4*k` for word *k* (the delivery testbench computes `byte_addr = word_index << 2`). Core fetch and data addresses are always word-aligned, so the core-visible window of each array is 4096 words (16 KB), indexed by `addr[13:2]`; the loader's arrays are 16384 words (64 KB) each, so AXIL traffic can additionally address the unaligned sub-word slots (`addr[1:0] != 0`) that the core never generates.
- **Aliasing.** Because the index is `addr[13:0]`, byte-address bits [15:14] are not decoded: the 64 KB byte-address window of each region aliases onto the array every `0x4000` bytes. Images must fit the 16 KB core-visible window per region (see Known Limitations, Chapter 6).
- **Address windowing.** The core presents full 32-bit addresses; only bits [16:14] region/array bits and [13:0] index bits are decoded. The core's `RESET_ADDR` must be chosen so its used range lands in the window (the loader testbench boots battery images linked at `0x8000_0000` with `RESET_ADDR = 0x8000_0000`, whose low 18 bits fall in the imem region).
- **Per-byte strobes.** Loader writes merge `fub_wdata` per `fub_wstrb` byte; core stores merge `dmem_wdata` per `dmem_wstrb` byte — the same rotated-strobe contract as the simulation memory.

## CTRL Register and Run Control

| Bits | Field | Access | Description |
|------|-------|--------|-------------|
| [0] | `run` | R (set by write) | 0 = load mode (power-on default): loader owns both RAM write ports, `core_rst_n` is low; 1 = run mode: the core owns the write ports, `core_rst_n` is high. Sticky until reset — writing 0 does not clear it |

: CTRL register (AXIL offset `0x0002_0000`)

`core_rst_n` is literally `run_q` inverted in role: it *is* the run bit. A CTRL write takes effect on the write commit cycle (W-channel fire); the core starts fetching `RESET_ADDR` the very cycle the run write commits.

## Mutual Exclusion (Load Mode vs Run Mode)

- **Load mode (`run == 0`):** the loader owns the RAM write ports; `ld_wr_fire = w_fire && !addr[CTRL] && !run_q` gates image writes. The core is held in reset (`core_rst_n = 0`), parks its fetch at `RESET_ADDR`, and retires nothing.
- **Run mode (`run == 1`):** the core owns both write ports (`core_wr_fire = run_q && dmem_req && (dmem_wstrb != 0)`); loader writes are dropped in logic — the B response still returns OKAY, but the array does not change (testplan scenario ML-09 pins this: an AXIL write to the halted core's ECALL word must not poison the fetch).
- **No arbiter.** Both clients merge into each array in one clocked process; protocol guarantees they are never both entitled at once.

## Programming Sequence

1. Assert `aresetn` low, then release it. The loader powers into load mode: `CTRL` reads 0, `core_rst_n` is low, the core is held.
2. Stream the program image over AXIL writes: instruction words to the imem region (byte offsets from `0x00000`), data (including `.tohost`/`.data`) to the addresses the image expects — with the unified map, data linked above `0x10000` lands in the dmem region automatically. Writes may be full-word or per-byte (`wstrb`).
3. (Optional but recommended) Read back critical words over the AXIL read port; reads work in both modes and see loader and core writes.
4. Write `CTRL.run = 1` (AXIL write of `0x0000_0001` to `0x0002_0000`). The core leaves reset immediately and fetches `RESET_ADDR` on the commit cycle — have any trace sampler armed *before* this write.
5. Observe execution: the core runs to its ECALL halt (`halt` rises with cause `0x1`, `gp == 1` on a successful riscv-tests-style program). Memory the core stores is readable back through the AXIL port in run mode (scenario ML-06).
6. To load a new image, reset the loader (`aresetn`): `run` clears, load mode re-enters.

---

**Last Updated:** 2026-10-07
