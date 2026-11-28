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

# hive_c_controller (Block 1)

The master controller: VexRiscv "Small" (RV32IM) plus the glue that turns
firmware decisions into CDA packets, control-network frames, and register
access. Clock domain: `hive_c_clk`.

```
hive_c_controller
├── hive_c_loader.sv         # core + both memories + AXIL load-then-run window (CORE_FLAVOR)
│   ├── hive_c_core_vexriscv.sv  # CORE_FLAVOR="vexriscv" glue: VexRiscv iBus/dBus -> core ports
│   ├── (hive_c_core_peregrine.sv)  # CORE_FLAVOR="peregrine" glue, not built yet
│   └── hive_c_bram.sv  x2   # 32 KB true-dual-port bank: I-mem, D-mem
├── descriptor_gen.sv        # CDA descriptor assembly + injection queue
├── axis4_master.sv          # AXIS TX (CDA) into delta_clk CDC FIFO
├── ctrl_net_master.sv       # Control-network command serializer
├── axil_master.sv           # AXI4-Lite master window (RAPIDS/Delta/engine-monitor cfg)
└── host_if.sv               # UART / AXI4-Lite slave command interface
```

: HIVE-C module tree

## Submodules

**`hive_c_loader`.** HIVE-C's core, its two memories and the firmware
loader in one block (implemented 2026-11-27, testplan `hive_c_loader`
LDR-01..05). It replaces the v0.2 tree's `vexriscv_wrapper`,
`instruction_mem` and `data_mem`. The loader follows the kestrel pattern
(decision below): an AXI4-Lite slave over both memories plus a CTRL run bit
that is the core's reset.

*Address map* (AXIL byte address, `AXIL_ADDR_WIDTH` >= 18, upper bits zero;
every access is a full aligned word):

| Address | What | Access |
|---------|------|--------|
| 0x0_0000 - 0x0_7FFF | I-mem bank | write in load mode only; read any time |
| 0x0_8000 - 0x0_FFFF | D-mem bank | write in load mode only; read any time |
| 0x2_0000 | CTRL | W bit 0 `run` (1 = release the core at 0x0000_0000, 0 = hold; reset 0). R {`active`[1], `run`[0]} |
| 0x2_0004 | BUILD_ID | RO, "HCVX" (vexriscv) / "HCPG" (peregrine) |
| anything else, or addr[1:0] != 0 | | SLVERR |

: hive_c_loader AXIL address map

The memory half of the window is the firmware memory map (HAS §4.3). A
memory write in run mode returns SLVERR and is dropped; so do unmapped,
unaligned and read-only accesses. This is a deliberate departure from
`kestrel_mem_loader` / `gatling_mem_bram`, which acknowledge a run-mode
write with OKAY and drop it: a host loader here sees its mistakes.

*Memories.* Two `hive_c_bram` banks, 32 KB each (`BANK_WORDS` = 8192),
true-dual-port block RAM with a registered read on both ports and no reset.
Port A is the core's fetch port. Port B is the core's data port in run mode
and the loader's otherwise. The two banks form one 64 KB space on every
port, selected by address bit 15, as `kestrel_mem_loader` does: the core can
load constants from I-mem and fetch from D-mem. A core access outside
0x0000_0000 - 0x0000_FFFF reads 0 and drops writes. The 0x4000_0000
peripheral windows (`axil_master`, the descriptor mailbox) are decoded by
`hive_c_controller` when it is integrated, not here (open item below).

*Arbitration.* Loader writes and the core never meet: a memory write needs
`active` = 0, which means the core is held. Loader reads and core data
accesses can meet on port B. The core always wins, and the loader's AR waits
a cycle (the read path is kestrel_mem_bram's: address, block RAM, holding
register).

**`CORE_FLAVOR` (PRD §10.3).** A string parameter selects the core:
`"vexriscv"` (the default, the only flavor built) or `"peregrine"`
(riscv-ip/peregrine-rv32im, the falcon-ladder successor; selecting it stops
elaboration until its glue is built, hive TASK-001). Everything except
the core's glue module is flavor-independent: the AXIL window, CTRL, the
banks, the arbitration and the testplan. The glue meets the rest of the
block at one seam:

- `run` in, `core_active` out. The glue owns the core's reset. `core_active`
  is high from the release until the core can no longer touch memory, and
  the loader gates its write window and the core's requests on it, never on
  `run`. CTRL reads it back as `active`.
- A fetch port (`f_req`, `f_addr` -> `f_rvalid`, `f_rdata`) and a data port
  (`d_req`, `d_wr`, `d_mask`, `d_addr`, `d_wdata` -> `d_rvalid`, `d_rdata`).
  A request is accepted in the cycle it is presented, and a read's word
  arrives one cycle later with an `rvalid` pulse.
- Observation outputs for the TB (`core_ibus_*`, `core_dbus_*` in
  `hive_c_loader`): accepted fetch and data requests.

`hive_c_core_vexriscv` is a direct map. With `cmd.ready` tied high, the
VexRiscv simple buses at latency 1 are this contract: `iBus_rsp_valid` and
`dBus_rsp_ready` are the rvalids, `dBus_cmd_payload_mask` is the byte write
enable, bus errors are tied off (HiveCGen has `catchAccessFault = false`),
and `reset = !run`, so `core_active = run`. Its fetch observation is in fetch
order and shows the wrong-path fetches after a taken jump.

*Planned peregrine glue* (`hive_c_core_peregrine`, nothing outside the glue
changes):

- Core: `peregrine_top` (I$ + amber D$ + CLINT + uncached port behind one
  AXI4 master), at `AXI_DW = 32` (legal, one lane), so no width converter.
  `RESET_ADDR = 0`; `irq_external` from the block's input, `irq_timer` /
  `irq_software` from peregrine's own CLINT (its `tb_irq_*` tied 0).
- Memory side: an AXI4 slave inside the glue, turning AR bursts into fetch
  port reads (I$ line fills) and AW/W bursts into data-port writes (D$
  writebacks), with R/B built from the one-cycle responses. Built from the
  `axi4_slave_rd` / `axi4_slave_wr` leaves the way this block uses the AXIL
  leaves. The AXI4 stays inside the glue, so HIVE's no-AXI4-at-a-block-
  boundary rule holds.
- Run: on `run` falling, the glue raises `dc_clean_req`, waits for
  `dc_clean_done`, then holds the core in reset and drops `core_active`.
  The D$ is write-back, so without the clean the loader would read stale
  results after a stop.
- Observation: fetch from RVFI (`rvfi_valid`, `rvfi_pc_rdata`, retire order),
  data from `dobs_*` (`dobs_wstrb` != 0 is a write).

**`descriptor_gen`.** Turns a firmware-written descriptor record (written
into a small command mailbox in data-memory space) into a 256-bit CDA beat:
field assembly per HAS §4.2, injection-FIFO push, and backpressure hold on
`tready`. Holds up to `MAX_INFLIGHT_DESCRIPTORS` outstanding descriptors;
full is a firmware-visible stall flag, not an error.

**`axis4_master`.** Drives the CDA AXIS interface into the 256×8 async FIFO
that crosses to `delta_clk`. Asserts `tuser=2'b01`, `tdest=16`, `tlast`
every beat. Single outstanding packet at a time (one descriptor = one beat).

**`ctrl_net_master`.** Serializes control-network commands from firmware:
command + target mask + payload into 32-bit frames, multicast capable for
broadcasts (`CONFIG_PREPARE`, `SET_ROUTING_MODE`, threshold updates).

**`axil_master`.** The 0x4000_0000 register window (HAS §4.3). Address
decode for the RAPIDS, Delta, engine-monitor (status and the gatling
loader window), and config regions; a
lightweight request/response queue so firmware never stalls on AXIL
handshake.

**`host_if`.** UART and/or AXI4-Lite slave command channel (synthesis
option). Normalizes both to the same internal command FIFO consumed by
firmware.

## Interfaces

External: host interface, CDA AXIS master (into CDC), control-network
master, AXIL master. Internal: memory buses (core-local), mailbox from
firmware view, interrupt lines in.

## Decisions (owner, 2026-10-13)

- **Firmware load transport: kestrel loader pattern.** HIVE-C adopts the
  rung-1 board-loader approach — an AXIL-slave loader with on-chip memories
  and load-then-run control, in the style of `kestrel_mem_loader` (see the
  kestrel MAS, `ch02_blocks/06_kestrel_mem_loader.md`). JTAG and
  preloaded-BRAM options are dropped.
- **Descriptor mailbox: parameter-controlled, dedicated register file is
  the default.** A synthesis parameter selects between a dedicated
  descriptor-register file and a data-memory aperture; RTL implements the
  register-file path first. The legacy spec's "custom instruction for
  atomic descriptor injection" alternative was considered and rejected —
  the mailbox + `descriptor_gen` model stands (policy stays in firmware;
  no VexRiscv plugin surgery).

## Open Items

- **Peripheral port.** `hive_c_loader` decodes only 0x0000_0000 -
  0x0000_FFFF. The HAS firmware map's 0x4000_0000 windows need a core data
  path out of the block (a peripheral port beside the data port) when
  `hive_c_controller` is integrated.
- **peregrine flavor, before it is built:**
  - peregrine's PRD P7 map has uncached I/O only at 0x1000_0000 -
    0x1FFF_FFFF and treats everything else as cacheable RAM, so HIVE's
    0x4000_0000 peripheral windows would go through the D$. Either the
    HIVE-C map moves for that flavor or peregrine's uncached window becomes
    a parameter. That is an owner decision, and it touches peregrine.
  - LDR-03's "store landed" readback needs the clean-on-stop above.
  - LDR-04's contention witness counts port-B collisions. Under peregrine
    those are AXI4 fill and writeback beats, not core accesses, so the test
    needs fill-heavy traffic for that check to bite.

---

**Last Updated:** 2026-11-27
