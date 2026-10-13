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
├── vexriscv_wrapper.sv      # VexRiscv instantiation + debug/irq plumbing
├── instruction_mem.sv       # 32 KB tightly-coupled I-mem (BRAM)
├── data_mem.sv              # 32 KB tightly-coupled D-mem (BRAM)
├── descriptor_gen.sv        # CDA descriptor assembly + injection queue
├── axis4_master.sv          # AXIS TX (CDA) into delta_clk CDC FIFO
├── ctrl_net_master.sv       # Control-network command serializer
├── axil_master.sv           # AXI4-Lite master window (RAPIDS/Delta/SERV cfg)
└── host_if.sv               # UART / AXI4-Lite slave command interface
```

: HIVE-C module tree

## Submodules

**`vexriscv_wrapper`.** Instantiates the generated VexRiscv core with the
"Small" configuration. Exposes JTAG or UART-based firmware load (open item:
loader transport — the falcon suite's kestrel loader pattern is the
preferred precedent), machine timer for the statistics interval, and the
interrupt aggregation from `interrupt.c`'s hardware sources (RAPIDS
completion, control-network alert, host command).

**`instruction_mem` / `data_mem`.** 32 KB each, single-cycle tightly-coupled
BRAM. Dual-ported where the loader needs a debug port; the core port always
wins arbitration.

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
decode for the RAPIDS, Delta, SERV-status, and config regions; a
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

None in this block.

---

**Last Updated:** 2026-10-13
