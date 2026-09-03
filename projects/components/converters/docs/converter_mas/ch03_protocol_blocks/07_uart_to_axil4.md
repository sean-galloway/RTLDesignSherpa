# 3.7 UART to AXI4-Lite Bridge

The `uart_to_axil4` block turns a two-wire serial link into an AXI4-Lite
master, so a host can read and write a design's register space over a USB
serial adapter with no JTAG, no debug core and no vendor tooling. It is the
access path the characterization harnesses use for board bring-up.

Three modules ship in `rtl/uart_to_axil4/`: the byte-level `uart_rx` and
`uart_tx`, and `uart_axil_bridge`, which parses commands and drives the bus.

## 3.7.1 Module Organization

`uart_axil_bridge` instantiates four blocks:

| Instance | Module | Role |
|----------|--------|------|
| `u_uart_rx` | `uart_rx` | Serial to byte, with a ready/valid handshake |
| `u_uart_tx` | `uart_tx` | Byte to serial |
| `u_axil_wr_timing` | `axil4_master_wr` | Write-channel skid isolation |
| `u_axil_rd_timing` | `axil4_master_rd` | Read-channel skid isolation |

The two `axil4_master_*` instances are the same AMBA library blocks documented
in the RTL AMBA AXI4-Lite book; the bridge does not hand-roll a bus master. The
`SKID_DEPTH_*` parameters below are passed straight through to them.

`uart_rx` and `uart_tx` use the `i_clk`/`i_rst_n` common-block naming while the
bridge presents `aclk`/`aresetn`. The bridge maps them directly -- there is one
clock domain and no CDC anywhere in this block.

## 3.7.2 Command Protocol

Commands are ASCII, terminated by newline:

| Command | Form | Response |
|---------|------|----------|
| Write | `W <addr_hex> <data_hex>\n` | `OK\n` |
| Read | `R <addr_hex>\n` | `0x<data_hex>\n` |

The command letter is **case-insensitive**: `w`/`W` and `r`/`R` are both
accepted.

Hex digits are consumed as nibbles and shifted in, with `' '`, `'\n'` and
`'\r'` skipped as separators. The field widths follow the bus parameters --
`ceil(AXIL_ADDR_WIDTH/4)` address digits and `ceil(AXIL_DATA_WIDTH/4)` data
digits, so 8 of each at the 32-bit defaults.

Because digits shift rather than fill a fixed field, **the parser does not
validate length**. Supplying too few digits left-aligns nothing and yields a
small address; supplying too many silently discards the oldest nibbles. The
host is responsible for sending exactly the digit count the bus width implies.

## 3.7.3 Error Responses Are Not Reported

**A write that returns `SLVERR` or `DECERR` still answers `OK`.** The bridge
brings `bresp` and `rresp` back from the two `axil4_master_*` instances into
`w_fub_bresp`/`w_fub_rresp`, and then never examines them: no state depends on
either signal, and the response text is chosen by command type alone. A failed
read returns `0x` followed by whatever was on `rdata`.

This is a limitation of the bridge, not of the bus -- the response codes are
present at the pins and correct. A host that needs to distinguish an error from
success must do it out of band (for example by reading back a status register
the target sets), or the bridge must be extended to encode the response.

## 3.7.4 Parameters

`uart_axil_bridge`:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `AXIL_ADDR_WIDTH` | 32 | AXI4-Lite address width; sets the address digit count |
| `AXIL_DATA_WIDTH` | 32 | AXI4-Lite data width; sets the data digit count and `m_axil_wstrb` width |
| `CLKS_PER_BIT` | 868 | Baud divisor, `aclk` cycles per bit. The default is 100 MHz / 115200 baud |
| `SKID_DEPTH_AR` | 2 | Passed to `axil4_master_rd` |
| `SKID_DEPTH_R` | 4 | Passed to `axil4_master_rd` |
| `SKID_DEPTH_AW` | 2 | Passed to `axil4_master_wr` |
| `SKID_DEPTH_W` | 4 | Passed to `axil4_master_wr` |
| `SKID_DEPTH_B` | 2 | Passed to `axil4_master_wr` |

: uart_axil_bridge Parameters

`uart_rx` and `uart_tx` each take one parameter, `CLKS_PER_BIT` (default 868),
with the same meaning.

## 3.7.5 Ports

### uart_axil_bridge

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `aclk` | 1 | Input | Bridge clock; also clocks both UART blocks |
| `aresetn` | 1 | Input | Active-low reset |
| `i_uart_rx` | 1 | Input | Serial receive line |
| `o_uart_tx` | 1 | Output | Serial transmit line |
| `m_axil_awaddr` | AXIL_ADDR_WIDTH | Output | Write address |
| `m_axil_awprot` | 3 | Output | Write protection attributes |
| `m_axil_awvalid` | 1 | Output | Write address valid |
| `m_axil_awready` | 1 | Input | Write address ready |
| `m_axil_wdata` | AXIL_DATA_WIDTH | Output | Write data |
| `m_axil_wstrb` | AXIL_DATA_WIDTH/8 | Output | Write byte strobes |
| `m_axil_wvalid` | 1 | Output | Write data valid |
| `m_axil_wready` | 1 | Input | Write data ready |
| `m_axil_bresp` | 2 | Input | Write response; accepted but not reported (3.7.3) |
| `m_axil_bvalid` | 1 | Input | Write response valid |
| `m_axil_bready` | 1 | Output | Write response ready |
| `m_axil_araddr` | AXIL_ADDR_WIDTH | Output | Read address |
| `m_axil_arprot` | 3 | Output | Read protection attributes |
| `m_axil_arvalid` | 1 | Output | Read address valid |
| `m_axil_arready` | 1 | Input | Read address ready |
| `m_axil_rdata` | AXIL_DATA_WIDTH | Input | Read data, returned in the `0x...` response |
| `m_axil_rresp` | 2 | Input | Read response; accepted but not reported (3.7.3) |
| `m_axil_rvalid` | 1 | Input | Read data valid |
| `m_axil_rready` | 1 | Output | Read data ready |

: uart_axil_bridge Ports

### uart_rx

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `i_clk` | 1 | Input | Clock |
| `i_rst_n` | 1 | Input | Active-low reset |
| `i_rx` | 1 | Input | Serial receive line |
| `o_rx_data` | 8 | Output | Received byte |
| `o_rx_valid` | 1 | Output | Byte valid |
| `i_rx_ready` | 1 | Input | Consumer ready |

: uart_rx Ports

### uart_tx

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `i_clk` | 1 | Input | Clock |
| `i_rst_n` | 1 | Input | Active-low reset |
| `o_tx` | 1 | Output | Serial transmit line |
| `i_tx_data` | 8 | Input | Byte to send |
| `i_tx_valid` | 1 | Input | Byte valid |
| `o_tx_ready` | 1 | Output | Transmitter ready for the next byte |

: uart_tx Ports
