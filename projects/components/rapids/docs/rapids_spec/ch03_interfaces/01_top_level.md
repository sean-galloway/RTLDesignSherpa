# RAPIDS Top-Level Interfaces v2.1 - CORRECTED & COMPLETE

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

### Network Master Interface v2.1 - CORRECTED
| Signal | IO | Description |
|--------|-----------|-------------|
| `network_src_mst_pkt_valid` | O | Network packet valid |
| `network_src_mst_pkt_ready` | I | Network ready to accept packet |
| `network_src_mst_pkt_data[511:0]` | O | **Network packet data (chunk_enables embedded at [510:495])** |
| `network_src_mst_pkt_type[1:0]` | O | Packet type |
| `network_src_mst_pkt_addr[7:0]` | O | Channel address |
| `network_src_mst_pkt_addr_par` | O | Address parity |
| `network_src_mst_pkt_eos` | O | End of stream marker |
| `network_src_mst_pkt_par` | O | Data parity |
| `network_src_mst_ack_valid` | I | Network ACK valid |
| `network_src_mst_ack_ready` | O | Ready to accept ACK |
| `network_src_mst_ack_ack[1:0]` | I | ACK type |
| `network_src_mst_ack_addr[7:0]` | I | ACK channel address |
| `network_src_mst_ack_addr_par` | I | ACK address parity |
| `network_src_mst_ack_par` | I | ACK parity |

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
| `axi_snk_desc_ar_prot[2:0]` | O | Protection attributes |
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

### Network Slave Interface v2.1 - CORRECTED
| Signal | IO | Description |
|--------|-----------|-------------|
| `network_snk_slv_pkt_valid` | I | Network packet valid |
| `network_snk_slv_pkt_ready` | O | Ready to accept packet |
| `network_snk_slv_pkt_data[511:0]` | I | **Network packet data (chunk_enables embedded at [510:495])** |
| `network_snk_slv_pkt_type[1:0]` | I | Packet type |
| `network_snk_slv_pkt_addr[7:0]` | I | Channel address |
| `network_snk_slv_pkt_addr_par` | I | Address parity |
| `network_snk_slv_pkt_eos` | I | End of stream marker |
| `network_snk_slv_pkt_par` | I | Data parity |
| `network_snk_slv_ack_valid` | O | Network ACK valid |
| `network_snk_slv_ack_ready` | I | Ready to accept ACK |
| `network_snk_slv_ack_ack[1:0]` | O | ACK type |
| `network_snk_slv_ack_addr[7:0]` | O | ACK channel address |
| `network_snk_slv_ack_addr_par` | O | ACK address parity |
| `network_snk_slv_ack_par` | O | ACK parity |

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

## Key Interface Changes from v2.0

### **REMOVED SIGNALS (Non-Standard):**
- ~~`network_*_pkt_chunk_enables[15:0]`~~ - Now embedded in `pkt_data[510:495]`
- ~~`network_*_pkt_ctrl[3:0]`~~ - Replaced by embedded format
- ~~EOL/EOD signals~~ - Removed from sink path (not used)

### **ADDED SIGNALS v2.1:**
- **Embedded chunk_enables** in `network_*_pkt_data[510:495]`
- **EOS markers** `network_*_pkt_eos` for stream boundary detection
- **Parity signals** for address and data error detection
- **Complete AXI4-Lite interfaces** for source/sink configuration
- **Monitor bus AXI4-Lite group** for event aggregation and filtering

### **Embedded Chunk Enables Format:**
```systemverilog
// Non-RAW Packet Data Layout:
pkt_data[511:0] bit allocation:
[511]     - Reserved (1 bit)
[510:495] - chunk_enables[15:0] (16 bits) ← EMBEDDED HERE
[494:480] - Control flags (15 bits)
[479:0]   - Data fields (15 × 32-bit chunks)

// RAW Packet Data Layout:
pkt_data[511:0] = Raw data (512 bits, chunk_enables not applicable)
```

## Interface Summary

### **Total AXI Interfaces:**
- **Source:** 3 AXI4 Masters (data read, ctrl write, desc read) + 1 AXI4-Lite Slave (config)
- **Sink:** 3 AXI4 Masters (data write, ctrl write, desc read) + 1 AXI4-Lite Slave (config)
- **Monitor:** 1 AXI4-Lite Master (write) + 2 AXI4-Lite Slaves (error read, config)

### **Total Network Interfaces:**
- **Source:** 1 Network Master (packet + ack)
- **Sink:** 1 Network Slave (packet + ack)

### **Key Features:**
- **v2.1 Network Protocol** with embedded chunk_enables
- **Comprehensive AXI4-Lite Configuration** for all subsystems
- **Monitor Bus Aggregation** with configurable filtering
- **Error/Interrupt Handling** via dedicated AXI4-Lite interface
- **Proper Clock/Reset** with `core_clk` and `core_rstn`