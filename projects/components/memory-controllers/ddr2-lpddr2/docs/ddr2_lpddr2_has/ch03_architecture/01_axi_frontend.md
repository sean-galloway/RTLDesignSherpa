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

# AXI4 Frontend

The AXI frontend comprises two modules: `axi4_slave` (channel handshake and decoupling) and `addr_mapper` (flat-address-to-DRAM-coordinates translation).

## `axi4_slave`

### Purpose

Absorb AXI4 channel pressure and decouple SoC-side handshake behavior from the controller's internal clock-aligned pipeline. The slave terminates the five AXI channels (AW, W, B, AR, R) and presents a simplified internal interface to the rest of the controller.

### Internal State

| Element                | Description                                     |
|------------------------|-------------------------------------------------|
| AW skid buffer         | 2-deep; absorbs back-pressure timing            |
| AR skid buffer         | 2-deep                                          |
| W skid buffer          | 2-deep                                          |
| B response FIFO        | Indexed by AXI ID; preserves per-ID order       |
| R response staging     | Per-ID burst beat buffer                        |

### Behavior

- Accepts AW transactions; emits an internal `txn_alloc` request to `addr_mapper` and `txn_queue`. Acknowledges AW once both downstream slots are reserved.
- AR transactions are handled identically.
- W beats stream into a write-data FIFO with the originating transaction ID attached.
- B and R responses come back from the controller core and are routed to their channels with the correct ID.

### Per-ID Ordering

AXI4 requires reads from the same ID to return in order, and writes from the same ID to commit in order. The slave preserves order **per ID**. Across IDs, out-of-order completion is permitted by default (controlled by the `AXI_OOO_ACROSS_IDS` parameter — defaults to `true`).

### Burst Splitting

AXI4 permits up to 256 beats per burst; a DRAM row contains `2^COL_WIDTH` columns. If an AXI burst exceeds the remaining columns in the current row, `axi4_slave` splits the burst at the row boundary. Splitting is transparent to the AXI master — internally, the burst is recorded as two transactions with a "continuation" flag that prevents the second half from being scheduled before the first completes.

### Backpressure

- AW `.ready` deasserts when the transaction queue is full or has no available slots for the requested burst size.
- AR `.ready` follows the same rule.
- W `.ready` deasserts when the write-data FIFO is full.
- R and B `.valid` follow standard AXI protocol; consumers may stall the channels indefinitely without affecting the controller core.

---

## `addr_mapper`

### Purpose

Translate a flat AXI address into DRAM coordinates `(bank, row, col)`. The mapping is parameterizable so the same module supports different memory geometries and different scheduling-friendly bank interleavings.

### Interfaces

**Inputs:**

- `axi_addr` — `AXI_ADDR_WIDTH` bits wide

**Outputs:**

- `bank` — `$clog2(NUM_BANKS)` bits
- `row` — `ROW_WIDTH` bits
- `col` — `COL_WIDTH` bits

### Mapping Function

The default mapping is row-major (column in the low bits, bank above, row above that):

```
axi_addr[AXI_ADDR_WIDTH-1 : ROW_WIDTH + BANK_WIDTH + COL_WIDTH] = unused
axi_addr[ROW_WIDTH + BANK_WIDTH + COL_WIDTH - 1 : BANK_WIDTH + COL_WIDTH] = row
axi_addr[BANK_WIDTH + COL_WIDTH - 1 : COL_WIDTH] = bank
axi_addr[COL_WIDTH - 1 : 0] = col
```

### Alternative Mappings

A parameter `ADDR_MAP_SCHEME` selects from three predefined mappings:

| Scheme              | Layout                                          | When to use                                        |
|---------------------|-------------------------------------------------|----------------------------------------------------|
| `ROW_MAJOR`         | row \| bank \| col                              | Default; good for streaming workloads              |
| `BANK_INTERLEAVE`   | row \| col \| bank                              | Improves bank-parallelism for random workloads     |
| `XOR_HASH`          | row \| bank ⊕ row_low \| col                    | Breaks pathological row-conflict patterns          |

### Relationship to the DFI BFM

This module mirrors the `AddressMapping` class in the DFI BFM (`src/CocoTBFramework/components/dfi/dfi_signals.py`). The same mapping object can drive both RTL elaboration and BFM verification, ensuring address-decode consistency between simulation and silicon.
