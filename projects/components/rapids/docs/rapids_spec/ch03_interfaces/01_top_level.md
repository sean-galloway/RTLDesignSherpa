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

# RAPIDS Top-Level Interfaces v3.0 - AXIS4 Migration

## Clock and Reset
| Signal | IO | Description |
|--------|-----------|-------------|
| `core_clk` | I | System clock |
| `core_rstn` | I | Active-low reset |

## Source Data Path

### AXI4 AR Master Interface (512-bit data)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axi_src_data_ar_valid` | O | Read address valid |
| `axi_src_data_ar_ready` | I | Read address ready |
| `axi_src_data_ar_addr[39:0]` | O | Read address |
| `axi_src_data_ar_len[7:0]` | O | Burst length - 1 |
| `axi_src_data_ar_size[2:0]` | O | Transfer size |
| `axi_src_data_ar_burst[1:0]` | O | Burst type |
| `axi_src_data_ar_id[7:0]` | O | Transaction ID |
| `axi_src_data_ar_lock` | O | Lock type |
| `axi_src_data_ar_cache[3:0]` | O | Cache attributes |
| `axi_src_data_ar_prot[2:0]` | O | Protection attributes |
| `axi_src_data_ar_qos[3:0]` | O | Quality of Service |
| `axi_src_data_ar_region[3:0]` | O | Region identifier |
| `axi_src_data_ar_user` | O | User-defined |
| `axi_src_data_r_valid` | I | Read data valid |
| `axi_src_data_r_ready` | O | Read data ready |
| `axi_src_data_r_data[511:0]` | I | Read data |
| `axi_src_data_r_id[7:0]` | I | Transaction ID |
| `axi_src_data_r_resp[1:0]` | I | Read response |
| `axi_src_data_r_last` | I | Last transfer in burst |
| `axi_src_data_r_user` | I | User-defined |

### AXI4 AW Master Interface (32-bit control data)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axi_src_ctrl_aw_valid` | O | Write address valid |
| `axi_src_ctrl_aw_ready` | I | Write address ready |
| `axi_src_ctrl_aw_addr[39:0]` | O | Write address |
| `axi_src_ctrl_aw_len[7:0]` | O | Burst length - 1 |
| `axi_src_ctrl_aw_size[2:0]` | O | Transfer size |
| `axi_src_ctrl_aw_burst[1:0]` | O | Burst type |
| `axi_src_ctrl_aw_id[7:0]` | O | Transaction ID |
| `axi_src_ctrl_aw_lock` | O | Lock type |
| `axi_src_ctrl_aw_cache[3:0]` | O | Cache attributes |
| `axi_src_ctrl_aw_prot[2:0]` | O | Protection attributes |
| `axi_src_ctrl_aw_qos[3:0]` | O | Quality of Service |
| `axi_src_ctrl_aw_region[3:0]` | O | Region identifier |
| `axi_src_ctrl_aw_user` | O | User-defined |
| `axi_src_ctrl_w_valid` | O | Write data valid |
| `axi_src_ctrl_w_ready` | I | Write data ready |
| `axi_src_ctrl_w_data[31:0]` | O | Write data |
| `axi_src_ctrl_w_strb[3:0]` | O | Write strobes |
| `axi_src_ctrl_w_last` | O | Last transfer in burst |
| `axi_src_ctrl_w_user` | O | User-defined |
| `axi_src_ctrl_b_valid` | I | Write response valid |
| `axi_src_ctrl_b_ready` | O | Write response ready |
| `axi_src_ctrl_b_id[7:0]` | I | Transaction ID |
| `axi_src_ctrl_b_resp[1:0]` | I | Write response |
| `axi_src_ctrl_b_user` | I | User-defined |

### AXI4 AR Master Interface (512-bit descriptor data)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axi_src_desc_ar_valid` | O | Read address valid |
| `axi_src_desc_ar_ready` | I | Read address ready |
| `axi_src_desc_ar_addr[39:0]` | O | Read address |
| `axi_src_desc_ar_len[7:0]` | O | Burst length - 1 |
| `axi_src_desc_ar_size[2:0]` | O | Transfer size |
| `axi_src_desc_ar_burst[1:0]` | O | Burst type |
| `axi_src_desc_ar_id[7:0]` | O | Transaction ID |
| `axi_src_desc_ar_lock` | O | Lock type |
| `axi_src_desc_ar_cache[3:0]` | O | Cache attributes |
| `axi_src_desc_ar_prot[2:0]` | O | Protection attributes |
| `axi_src_desc_ar_qos[3:0]` | O | Quality of Service |
| `axi_src_desc_ar_region[3:0]` | O | Region identifier |
| `axi_src_desc_ar_user` | O | User-defined |
| `axi_src_desc_r_valid` | I | Read data valid |
| `axi_src_desc_r_ready` | O | Read data ready |
| `axi_src_desc_r_data[511:0]` | I | Read data |
| `axi_src_desc_r_id[7:0]` | I | Transaction ID |
| `axi_src_desc_r_resp[1:0]` | I | Read response |
| `axi_src_desc_r_last` | I | Last transfer in burst |
| `axi_src_desc_r_user` | I | User-defined |

### AXI4-Lite Slave Interface (Source Configuration)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axil_src_cfg_aw_valid` | I | Write address valid |
| `axil_src_cfg_aw_ready` | O | Write address ready |
| `axil_src_cfg_aw_addr[39:0]` | I | Write address |
| `axil_src_cfg_aw_prot[2:0]` | I | Protection attributes |
| `axil_src_cfg_w_valid` | I | Write data valid |
| `axil_src_cfg_w_ready` | O | Write data ready |
| `axil_src_cfg_w_data[31:0]` | I | Write data |
| `axil_src_cfg_w_strb[3:0]` | I | Write strobes |
| `axil_src_cfg_b_valid` | O | Write response valid |
| `axil_src_cfg_b_ready` | I | Write response ready |
| `axil_src_cfg_b_resp[1:0]` | O | Write response |
| `axil_src_cfg_ar_valid` | I | Read address valid |
| `axil_src_cfg_ar_ready` | O | Read address ready |
| `axil_src_cfg_ar_addr[39:0]` | I | Read address |
| `axil_src_cfg_ar_prot[2:0]` | I | Protection attributes |
| `axil_src_cfg_r_valid` | O | Read data valid |
| `axil_src_cfg_r_ready` | I | Read data ready |
| `axil_src_cfg_r_data[31:0]` | O | Read data |
| `axil_src_cfg_r_resp[1:0]` | O | Read response |

### AXI4-Stream Master Interface (TX) - NEW v3.0
| Signal | IO | Description |
|--------|-----------|-------------|
| `axis_src_tx_tdata[511:0]` | O | Stream data payload |
| `axis_src_tx_tstrb[63:0]` | O | Byte strobes (write enables) |
| `axis_src_tx_tlast` | O | Last transfer in packet |
| `axis_src_tx_tvalid` | O | Stream data valid |
| `axis_src_tx_tready` | I | Stream ready (backpressure) |
| `axis_src_tx_tuser[15:0]` | O | User sideband (packet metadata) |

**TUSER Encoding (Source TX):**
```
[15:8] - Reserved for future use
[7:0]  - Packet type/flags
```

**Note:** AXIS uses standard `tstrb` for byte-level validity instead of custom chunk_enables. All credits and ACK mechanisms removed from streaming interface.

## Sink Data Path

### AXI4 AW Master Interface (512-bit data)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axi_snk_data_aw_valid` | O | Write address valid |
| `axi_snk_data_aw_ready` | I | Write address ready |
| `axi_snk_data_aw_addr[39:0]` | O | Write address |
| `axi_snk_data_aw_len[7:0]` | O | Burst length - 1 |
| `axi_snk_data_aw_size[2:0]` | O | Transfer size |
| `axi_snk_data_aw_burst[1:0]` | O | Burst type |
| `axi_snk_data_aw_id[7:0]` | O | Transaction ID |
| `axi_snk_data_aw_lock` | O | Lock type |
| `axi_snk_data_aw_cache[3:0]` | O | Cache attributes |
| `axi_snk_data_aw_prot[2:0]` | O | Protection attributes |
| `axi_snk_data_aw_qos[3:0]` | O | Quality of Service |
| `axi_snk_data_aw_region[3:0]` | O | Region identifier |
| `axi_snk_data_aw_user` | O | User-defined |
| `axi_snk_data_w_valid` | O | Write data valid |
| `axi_snk_data_w_ready` | I | Write data ready |
| `axi_snk_data_w_data[511:0]` | O | Write data |
| `axi_snk_data_w_strb[63:0]` | O | Write strobes |
| `axi_snk_data_w_last` | O | Last transfer in burst |
| `axi_snk_data_w_user` | O | User-defined |
| `axi_snk_data_b_valid` | I | Write response valid |
| `axi_snk_data_b_ready` | O | Write response ready |
| `axi_snk_data_b_id[7:0]` | I | Transaction ID |
| `axi_snk_data_b_resp[1:0]` | I | Write response |
| `axi_snk_data_b_user` | I | User-defined |

### AXI4 AW Master Interface (32-bit control data)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axi_snk_ctrl_aw_valid` | O | Write address valid |
| `axi_snk_ctrl_aw_ready` | I | Write address ready |
| `axi_snk_ctrl_aw_addr[39:0]` | O | Write address |
| `axi_snk_ctrl_aw_len[7:0]` | O | Burst length - 1 |
| `axi_snk_ctrl_aw_size[2:0]` | O | Transfer size |
| `axi_snk_ctrl_aw_burst[1:0]` | O | Burst type |
| `axi_snk_ctrl_aw_id[7:0]` | O | Transaction ID |
| `axi_snk_ctrl_aw_lock` | O | Lock type |
| `axi_snk_ctrl_aw_cache[3:0]` | O | Cache attributes |
| `axi_snk_ctrl_aw_prot[2:0]` | O | Protection attributes |
| `axi_snk_ctrl_aw_qos[3:0]` | O | Quality of Service |
| `axi_snk_ctrl_aw_region[3:0]` | O | Region identifier |
| `axi_snk_ctrl_aw_user` | O | User-defined |
| `axi_snk_ctrl_w_valid` | O | Write data valid |
| `axi_snk_ctrl_w_ready` | I | Write data ready |
| `axi_snk_ctrl_w_data[31:0]` | O | Write data |
| `axi_snk_ctrl_w_strb[3:0]` | O | Write strobes |
| `axi_snk_ctrl_w_last` | O | Last transfer in burst |
| `axi_snk_ctrl_w_user` | O | User-defined |
| `axi_snk_ctrl_b_valid` | I | Write response valid |
| `axi_snk_ctrl_b_ready` | O | Write response ready |
| `axi_snk_ctrl_b_id[7:0]` | I | Transaction ID |
| `axi_snk_ctrl_b_resp[1:0]` | I | Write response |
| `axi_snk_ctrl_b_user` | I | User-defined |

### AXI4 AR Master Interface (512-bit descriptor data)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axi_snk_desc_ar_valid` | O | Read address valid |
| `axi_snk_desc_ar_ready` | I | Read address ready |
| `axi_snk_desc_ar_addr[39:0]` | O | Read address |
| `axi_snk_desc_ar_len[7:0]` | O | Burst length - 1 |
| `axi_snk_desc_ar_size[2:0]` | O | Transfer size |
| `axi_snk_desc_ar_burst[1:0]` | O | Burst type |
| `axi_snk_desc_ar_id[7:0]` | O | Transaction ID |
| `axi_snk_desc_ar_lock` | O | Lock type |
| `axi_snk_desc_ar_cache[3:0]` | O | Cache attributes |
| `axi_snk_desc_ar_prot[2:0]` | Protection attributes |
| `axi_snk_desc_ar_qos[3:0]` | O | Quality of Service |
| `axi_snk_desc_ar_region[3:0]` | O | Region identifier |
| `axi_snk_desc_ar_user` | O | User-defined |
| `axi_snk_desc_r_valid` | I | Read data valid |
| `axi_snk_desc_r_ready` | O | Read data ready |
| `axi_snk_desc_r_data[511:0]` | I | Read data |
| `axi_snk_desc_r_id[7:0]` | I | Transaction ID |
| `axi_snk_desc_r_resp[1:0]` | I | Read response |
| `axi_snk_desc_r_last` | I | Last transfer in burst |
| `axi_snk_desc_r_user` | I | User-defined |

### AXI4-Lite Slave Interface (Sink Configuration)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axil_snk_cfg_aw_valid` | I | Write address valid |
| `axil_snk_cfg_aw_ready` | O | Write address ready |
| `axil_snk_cfg_aw_addr[39:0]` | I | Write address |
| `axil_snk_cfg_aw_prot[2:0]` | I | Protection attributes |
| `axil_snk_cfg_w_valid` | I | Write data valid |
| `axil_snk_cfg_w_ready` | O | Write data ready |
| `axil_snk_cfg_w_data[31:0]` | I | Write data |
| `axil_snk_cfg_w_strb[3:0]` | I | Write strobes |
| `axil_snk_cfg_b_valid` | O | Write response valid |
| `axil_snk_cfg_b_ready` | I | Write response ready |
| `axil_snk_cfg_b_resp[1:0]` | O | Write response |
| `axil_snk_cfg_ar_valid` | I | Read address valid |
| `axil_snk_cfg_ar_ready` | O | Read address ready |
| `axil_snk_cfg_ar_addr[39:0]` | I | Read address |
| `axil_snk_cfg_ar_prot[2:0]` | I | Protection attributes |
| `axil_snk_cfg_r_valid` | O | Read data valid |
| `axil_snk_cfg_r_ready` | I | Read data ready |
| `axil_snk_cfg_r_data[31:0]` | O | Read data |
| `axil_snk_cfg_r_resp[1:0]` | O | Read response |

### AXI4-Stream Slave Interface (RX) - NEW v3.0
| Signal | IO | Description |
|--------|-----------|-------------|
| `axis_snk_rx_tdata[511:0]` | I | Stream data payload |
| `axis_snk_rx_tstrb[63:0]` | I | Byte strobes (write enables) |
| `axis_snk_rx_tlast` | I | Last transfer in packet |
| `axis_snk_rx_tvalid` | I | Stream data valid |
| `axis_snk_rx_tready` | O | Stream ready (backpressure) |
| `axis_snk_rx_tuser[15:0]` | I | User sideband (packet metadata) |

**TUSER Encoding (Sink RX):**
```
[15:8] - Reserved for future use
[7:0]  - Packet type/flags
```

**Note:** AXIS uses standard `tstrb` for byte-level validity instead of custom chunk_enables. All credits and ACK mechanisms removed from streaming interface.

## Monitor Bus AXI4-Lite Group Interfaces

### AXI4-Lite Slave Interface (Error/Interrupt Read)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axil4_mon_err_ar_valid` | I | Read address valid |
| `axil4_mon_err_ar_ready` | O | Read address ready |
| `axil4_mon_err_ar_addr[31:0]` | I | Read address |
| `axil4_mon_err_ar_prot[2:0]` | I | Protection attributes |
| `axil4_mon_err_r_valid` | O | Read data valid |
| `axil4_mon_err_r_ready` | I | Read data ready |
| `axil4_mon_err_r_data[63:0]` | O | Read data (64-bit monitor packets) |
| `axil4_mon_err_r_resp[1:0]` | O | Read response |

### AXI4-Lite Master Interface (Monitor Write)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axil4_mon_wr_aw_valid` | O | Write address valid |
| `axil4_mon_wr_aw_ready` | I | Write address ready |
| `axil4_mon_wr_aw_addr[31:0]` | O | Write address |
| `axil4_mon_wr_aw_prot[2:0]` | O | Protection attributes |
| `axil4_mon_wr_w_valid` | O | Write data valid |
| `axil4_mon_wr_w_ready` | I | Write data ready |
| `axil4_mon_wr_w_data[31:0]` | O | Write data |
| `axil4_mon_wr_w_strb[3:0]` | O | Write strobes |
| `axil4_mon_wr_b_valid` | I | Write response valid |
| `axil4_mon_wr_b_ready` | O | Write response ready |
| `axil4_mon_wr_b_resp[1:0]` | I | Write response |

### AXI4-Lite Slave Interface (Monitor Configuration)
| Signal | IO | Description |
|--------|-----------|-------------|
| `axil4_mon_cfg_aw_valid` | I | Write address valid |
| `axil4_mon_cfg_aw_ready` | O | Write address ready |
| `axil4_mon_cfg_aw_addr[31:0]` | I | Write address |
| `axil4_mon_cfg_aw_prot[2:0]` | I | Protection attributes |
| `axil4_mon_cfg_w_valid` | I | Write data valid |
| `axil4_mon_cfg_w_ready` | O | Write data ready |
| `axil4_mon_cfg_w_data[31:0]` | I | Write data |
| `axil4_mon_cfg_w_strb[3:0]` | I | Write strobes |
| `axil4_mon_cfg_b_valid` | O | Write response valid |
| `axil4_mon_cfg_b_ready` | I | Write response ready |
| `axil4_mon_cfg_b_resp[1:0]` | O | Write response |
| `axil4_mon_cfg_ar_valid` | I | Read address valid |
| `axil4_mon_cfg_ar_ready` | O | Read address ready |
| `axil4_mon_cfg_ar_addr[31:0]` | I | Read address |
| `axil4_mon_cfg_ar_prot[2:0]` | I | Protection attributes |
| `axil4_mon_cfg_r_valid` | O | Read data valid |
| `axil4_mon_cfg_r_ready` | I | Read data ready |
| `axil4_mon_cfg_r_data[31:0]` | O | Read data |
| `axil4_mon_cfg_r_resp[1:0]` | O | Read response |

## Key Interface Changes from v2.1 to v3.0

### **REMOVED - Custom Network Protocol:**
- ~~`network_*_pkt_valid/ready`~~ - Replaced by standard `axis_*_tvalid/tready`
- ~~`network_*_pkt_data[511:0]`~~ - Replaced by `axis_*_tdata[511:0]`
- ~~`network_*_pkt_type[1:0]`~~ - Moved to `axis_*_tuser[7:0]`
- ~~`network_*_pkt_addr[7:0]`~~ - Removed (no addressing in streaming)
- ~~`network_*_pkt_addr_par`~~ - Removed (parity optional via TUSER if needed)
- ~~`network_*_pkt_eos`~~ - Replaced by `axis_*_tlast`
- ~~`network_*_pkt_par`~~ - Removed (parity optional via TUSER if needed)
- ~~**ALL ACK signals**~~ - Removed completely (no credit/ACK on streaming)
  - ~~`network_*_ack_valid/ready`~~
  - ~~`network_*_ack_ack[1:0]`~~
  - ~~`network_*_ack_addr[7:0]`~~
  - ~~`network_*_ack_addr_par`~~
  - ~~`network_*_ack_par`~~
- ~~Embedded chunk_enables format~~ - Replaced by standard `axis_*_tstrb[63:0]`

### **ADDED - Standard AXIS4 Protocol:**
- **`axis_src_tx_tdata[511:0]`** - Source TX data stream
- **`axis_src_tx_tstrb[63:0]`** - Byte-level write enables (64 bytes for 512-bit bus)
- **`axis_src_tx_tlast`** - Packet boundary marker
- **`axis_src_tx_tvalid/tready`** - Standard handshake protocol
- **`axis_src_tx_tuser[15:0]`** - Optional metadata sideband
- **`axis_snk_rx_tdata[511:0]`** - Sink RX data stream
- **`axis_snk_rx_tstrb[63:0]`** - Byte-level write enables
- **`axis_snk_rx_tlast`** - Packet boundary marker
- **`axis_snk_rx_tvalid/tready`** - Standard handshake protocol
- **`axis_snk_rx_tuser[15:0]`** - Optional metadata sideband

### **Migration Benefits:**
1. **Industry Standard**: AXIS4 is widely supported, well-documented standard protocol
2. **Simplified Flow Control**: Standard `tvalid/tready` backpressure, no custom ACK channels
3. **Cleaner Byte Qualification**: Standard `tstrb` replaces embedded chunk_enables
4. **Packet Framing**: Standard `tlast` replaces custom EOS markers
5. **Reduced Complexity**: Eliminated custom packet types, addresses, parity, ACK logic
6. **Tool Support**: Better IP integration, simulation, and verification tool support
7. **No Interface Credits**: Simplified interface - credits remain only in scheduler (internal)

### **AXIS4 vs Custom Network Protocol Mapping:**

| Custom Network v2.1 | AXIS4 v3.0 | Notes |
|---------------------|------------|-------|
| `network_*_pkt_data[511:0]` | `axis_*_tdata[511:0]` | Direct data payload |
| `network_*_pkt_chunk_enables[15:0]` (embedded) | `axis_*_tstrb[63:0]` | Byte-level granularity |
| `network_*_pkt_eos` | `axis_*_tlast` | Standard packet boundary |
| `network_*_pkt_valid/ready` | `axis_*_tvalid/tready` | Standard handshake |
| `network_*_pkt_type[1:0]` | `axis_*_tuser[7:0]` | Metadata in sideband |
| `network_*_pkt_addr[7:0]` | **REMOVED** | No addressing in streaming |
| `network_*_pkt_par` | **REMOVED** | Optional via TUSER if needed |
| `network_*_ack_*` (all) | **REMOVED** | No ACK/credit on interface |

## Interface Summary

### **Total AXI Interfaces:**
- **Source:** 3 AXI4 Masters (data read, ctrl write, desc read) + 1 AXI4-Lite Slave (config)
- **Sink:** 3 AXI4 Masters (data write, ctrl write, desc read) + 1 AXI4-Lite Slave (config)
- **Monitor:** 1 AXI4-Lite Master (write) + 2 AXI4-Lite Slaves (error read, config)

### **Total AXIS Interfaces (NEW v3.0):**
- **Source:** 1 AXIS4 Master (TX streaming)
- **Sink:** 1 AXIS4 Slave (RX streaming)

### **Key Features:**
- **Standard AXIS4 Protocol** for high-bandwidth streaming
- **Comprehensive AXI4-Lite Configuration** for all subsystems
- **Monitor Bus Aggregation** with configurable filtering
- **Error/Interrupt Handling** via dedicated AXI4-Lite interface
- **Proper Clock/Reset** with `core_clk` and `core_rstn`
- **Simplified Flow Control** - No custom ACK or credit mechanisms on streaming interfaces
- **Industry-Standard Interfaces** - Better tool support and IP reuse

## AXIS Data Path Integration

### Source Data Path (Memory -> AXIS TX):
```
AXI4 Read Master (512-bit)
    ↓ Read data from system memory
Source SRAM Control
    ↓ Buffer management
AXIS Master (rtl/amba/axis/axis_master.sv)
    ↓ axis_src_tx_* signals
External AXIS Receiver
```

**Key Points:**
- SRAM control writes to `axis_master` FUB interface (`fub_axis_tdata/tstrb/tlast/tvalid`)
- AXIS master outputs external `m_axis_*` signals
- Backpressure: `axis_src_tx_tready=0` -> SRAM control stalls
- Packet framing: SRAM sets `tlast` on final beat

### Sink Data Path (AXIS RX -> Memory):
```
External AXIS Transmitter
    ↓ axis_snk_rx_* signals
AXIS Slave (rtl/amba/axis/axis_slave.sv)
    ↓ Internal FUB interface
Sink SRAM Control
    ↓ Buffer management
AXI4 Write Master (512-bit)
    ↓ Write to system memory
```

**Key Points:**
- AXIS slave receives external `s_axis_*` signals
- Outputs to SRAM via FUB interface (`fub_axis_tdata/tstrb/tlast/tvalid`)
- Backpressure: SRAM full -> `axis_snk_rx_tready=0` -> upstream stalls
- Packet framing: `tlast=1` triggers SRAM to finalize packet

**See: See:**
- `ch03_interfaces/04_axis4_interface_spec.md` - Complete AXIS4 specification
- `rtl/amba/axis/axis_master.sv` - AXIS master RTL
- `rtl/amba/axis/axis_slave.sv` - AXIS slave RTL
