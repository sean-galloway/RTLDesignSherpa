# APB_XBAR_THIN

## Module: rtl/axi/apb_xbar_thin.sv

This Verilog module implements an APB crossbar switch, which serves as an interconnect between multiple APB masters and APB slaves. The crossbar enables concurrent transactions from masters to different slaves and includes an address decoder and weighted round-robin arbitration for conflict resolution when multiple masters request the same slave. This is a "thin" version of the router. It should be ok to use when all of the APB ports are physically near each and the when the frequency is slow.

### Parameters

- `M` (int): The number of APB masters connected to the crossbar. Default is 2.
- `S` (int): The number of APB slaves connected to the crossbar. Default is 4.
- `ADDR_WIDTH` (int): The width of the address bus. Default is 32 bits.
- `DATA_WIDTH` (int): The width of the data bus. Default is 32 bits.
- `STRB_WIDTH` (int): The width of the strobe signal which is derived from `DATA_WIDTH/8`.
- `MAX_THRESH` (int): Maximum threshold for the weighted round-robin arbiter. Default is 16.
- Additional local abbreviations like `DW`, `AW`, `SW`, `MTW`, and `MXMTW` for internal calculations.

### Ports

#### Input Ports

- `aclk`: APB clock signal.
- `aresetn`: Active low asynchronous reset.
- `SLAVE_ENABLE[S-1:0]`: Bitmask indicating which of the slaves are enabled.
- `SLAVE_ADDR_BASE[S-1:0][ADDR_WIDTH-1:0]`: Base address for each slave.
- `SLAVE_ADDR_LIMIT[S-1:0][ADDR_WIDTH-1:0]`: Address limit for each slave.
- `THRESHOLDS[MXMTW-1:0]`: Thresholds for the Weighted Round Robin Arbiter.
- Master interface ports which include `psel`, `penable`, `pwrite`, `pprot`, `paddr`, `pwdata`, and `pstrb`, each of which are sized according to the number of masters `M`.

#### Output Ports

- Master response ports: `pready`, `prdata`, and `pslverr`, each sized according to the number of masters `M`.
- Slave interface ports: `psel`, `penable`, `pwrite`, `pprot`, `paddr`, `pwdata`, and `pstrb`, each sized according to the number of slaves `S`.

### Internal Functionality

1. The module starts with initializing a debug log file.
2. Address decoding logic is implemented to determine which master is requesting access to which slave based on the address range.
3. Instantiation of weighted round robin arbiters for each slave to manage concurrent requests from multiple masters.
4. Multiplexing logic to route master requests to the correct slave based on arbiter decisions.
5. Multiple always_comb blocks are defined for debugging purposes to log activities at different stages of processing.
6. The demultiplexing logic for routing responses from slaves back to the requesting masters.

### Usage

The `apb_xbar_thin` module should be used in a system with multiple APB masters and slaves when there is a need for an interconnect mechanism to allow masters to communicate with slaves. Clock (`aclk`), reset (`aresetn`), and configuration signals (such as `SLAVE_ENABLE`, `SLAVE_ADDR_BASE`, etc.) should be correctly connected for the crossbar to function properly.

---

[Return to Index](index.md)

---
