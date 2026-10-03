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

# AXI4 Job Adapter

Generated at an end when its `*_IF` parameter is `"AXI4"`. The intake form is
a read engine: a job names a source address and a byte count, the engine
issues AXI4 read bursts and presents the returned data as the core's input
stream, inserting `last` every n (decoder) or k (encoder) symbols. The outlet
form is a write engine: it drains the core's output stream into AXI4 write
bursts at the job's destination address, one block at a time, and reports
each block's status in its completion. A job controller sequences the two.

## Job interface

Jobs arrive from the register block (chapter 4.4) -- source, destination,
count, kick -- or, with `JOB_IF = "DESC"`, from a small AXI-Stream descriptor
port carrying the same fields for chained jobs.

| Field | Width | Meaning |
|---|---|---|
| `src_addr` | `AXI_ADDR_WIDTH` | read engine start address (intake = AXI4) |
| `dst_addr` | `AXI_ADDR_WIDTH` | write engine start address (outlet = AXI4) |
| `byte_count` | 32 | bytes to read; must be a whole number of blocks |
| `kick` / `done` | 1 / 1 | start; completion pulse with the job's status summary |
| `cfg_erasure` | `N_SYMBOLS` | decoder only, `ERASURE_SUPPORT = 1`: job-level erasure bitmap, sampled at `cfg_start` and sliced per beat by the same beat index that builds `keep` -- the shape an MC known-bad column has (a fixed position set, identical in every block of the job) |

: Table 4.6: Job fields

The AXI-Stream adapter's erasure sideband is per-beat because a mid-stream
producer knows symbol positions only as the beat passes; the job adapter's is
per-job because a memory controller learns a bad column once and applies it
to everything it fetches. Both land on the core's same `in_erasure` port.

## AXI4 master ports

Each engine presents one AXI4 master (read-only or write-only) through the
house `axi4_master_rd` / `axi4_master_wr` timing wrapper: `AXI_ID_WIDTH`,
`AXI_ADDR_WIDTH`, `AXI_DATA_WIDTH` (= `DATA_WIDTH`), incrementing bursts up
to `cfg_xfer_beats`, no narrow transfers. Responses other than OKAY are
counted and reported in the job's done status; the data are still passed.

## Parameters

| Parameter | Default | Meaning |
|---|---|---|
| `AXI_ADDR_WIDTH` | 32 | address width |
| `AXI_ID_WIDTH` | 4 | ID width; the engines use one ID |
| `AXI_MAX_BURST_BEATS` | 16 | burst cap (`cfg_xfer_beats` may lower it at run time) |
| `JOB_IF` | `"REGS"` | `"REGS"` or `"DESC"` |
| `AXI_MONITOR` | 0 | 1 attaches the `_monlite` wrapper variant |

: Table 4.7: AXI4 job adapter parameters

## Behaviour

The read engine is modelled on STREAM's `axi_read_engine` and the write
engine on its `axi_write_engine` -- job valid/address/count in, done strobe
out, a burst cap -- reduced from STREAM's multi-channel, SRAM-coupled form to
one job and a FIFO. Whether that is a reduction of STREAM's modules or a
fresh instantiation is decided when the adapter is built. The job controller
hands the write engine each block's destination before the block's first
symbol reaches it, so a decoder job's output blocks land contiguously with
the parity removed.
