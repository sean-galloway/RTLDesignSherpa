#!/usr/bin/env python3
"""
Bridge: AXI4 Full Crossbar Generator (Framework Version)
Generates parameterized AXI4 crossbars using the unified verilog framework

Bridge connects masters and slaves across the divide, enabling high-performance
memory-mapped interconnects with out-of-order transaction support.

Author: RTL Design Sherpa
Project: Bridge (AXI4 Full Crossbar Generator)
Version: 1.0 (Framework-based, skeleton)
"""

import argparse
import sys
import os
import math
from dataclasses import dataclass
from typing import Tuple, Dict
from pathlib import Path

# Import the framework
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'bin'))
from rtl_generators.verilog.module import Module


@dataclass
class BridgeConfig:
    """Configuration for AXI4 crossbar generation"""
    num_masters: int        # Number of master interfaces
    num_slaves: int         # Number of slave interfaces
    data_width: int         # Data bus width in bits
    addr_width: int         # Address bus width in bits
    id_width: int           # Transaction ID width in bits
    address_map: Dict[int, Dict]  # Address ranges per slave
    pipeline_outputs: bool = True  # Register slave outputs
    enable_counters: bool = True   # Performance counters


class BridgeFlatCrossbar(Module):
    """
    AXI4 Full Crossbar Generator using Module framework

    Key Differences from Delta (AXIS):
    1. 5 independent channels (AW, W, B, AR, R) vs 1 channel
    2. Address range decode vs TDEST decode
    3. ID-based response routing (B, R channels)
    4. Transaction tracking tables for out-of-order support
    5. Separate read/write arbitration
    """

    def __init__(self, config: BridgeConfig):
        self.cfg = config
        self.module_str = f'bridge_axi4_flat_{config.num_masters}x{config.num_slaves}'

        # Initialize Module base class
        Module.__init__(self, module_name=self.module_str)

        # Define parameters
        param_str = f'''
            parameter int NUM_MASTERS = {config.num_masters},
            parameter int NUM_SLAVES  = {config.num_slaves},
            parameter int DATA_WIDTH  = {config.data_width},
            parameter int ADDR_WIDTH  = {config.addr_width},
            parameter int ID_WIDTH    = {config.id_width},
            parameter int STRB_WIDTH  = {config.data_width // 8}
        '''
        self.params.add_param_string(param_str)

        # Define ports (all 5 AXI4 channels for M masters and S slaves)
        port_str = f'''
            input  logic aclk,
            input  logic aresetn,

            // Master Interfaces - Write Address Channel (AW)
            input  logic [ADDR_WIDTH-1:0]   s_axi_awaddr  [NUM_MASTERS],
            input  logic [ID_WIDTH-1:0]     s_axi_awid    [NUM_MASTERS],
            input  logic [7:0]              s_axi_awlen   [NUM_MASTERS],
            input  logic [2:0]              s_axi_awsize  [NUM_MASTERS],
            input  logic [1:0]              s_axi_awburst [NUM_MASTERS],
            input  logic                    s_axi_awlock  [NUM_MASTERS],
            input  logic [3:0]              s_axi_awcache [NUM_MASTERS],
            input  logic [2:0]              s_axi_awprot  [NUM_MASTERS],
            input  logic                    s_axi_awvalid [NUM_MASTERS],
            output logic                    s_axi_awready [NUM_MASTERS],

            // Master Interfaces - Write Data Channel (W)
            input  logic [DATA_WIDTH-1:0]   s_axi_wdata  [NUM_MASTERS],
            input  logic [STRB_WIDTH-1:0]   s_axi_wstrb  [NUM_MASTERS],
            input  logic                    s_axi_wlast  [NUM_MASTERS],
            input  logic                    s_axi_wvalid [NUM_MASTERS],
            output logic                    s_axi_wready [NUM_MASTERS],

            // Master Interfaces - Write Response Channel (B)
            output logic [ID_WIDTH-1:0]     s_axi_bid    [NUM_MASTERS],
            output logic [1:0]              s_axi_bresp  [NUM_MASTERS],
            output logic                    s_axi_bvalid [NUM_MASTERS],
            input  logic                    s_axi_bready [NUM_MASTERS],

            // Master Interfaces - Read Address Channel (AR)
            input  logic [ADDR_WIDTH-1:0]   s_axi_araddr  [NUM_MASTERS],
            input  logic [ID_WIDTH-1:0]     s_axi_arid    [NUM_MASTERS],
            input  logic [7:0]              s_axi_arlen   [NUM_MASTERS],
            input  logic [2:0]              s_axi_arsize  [NUM_MASTERS],
            input  logic [1:0]              s_axi_arburst [NUM_MASTERS],
            input  logic                    s_axi_arlock  [NUM_MASTERS],
            input  logic [3:0]              s_axi_arcache [NUM_MASTERS],
            input  logic [2:0]              s_axi_arprot  [NUM_MASTERS],
            input  logic                    s_axi_arvalid [NUM_MASTERS],
            output logic                    s_axi_arready [NUM_MASTERS],

            // Master Interfaces - Read Data Channel (R)
            output logic [DATA_WIDTH-1:0]   s_axi_rdata  [NUM_MASTERS],
            output logic [ID_WIDTH-1:0]     s_axi_rid    [NUM_MASTERS],
            output logic [1:0]              s_axi_rresp  [NUM_MASTERS],
            output logic                    s_axi_rlast  [NUM_MASTERS],
            output logic                    s_axi_rvalid [NUM_MASTERS],
            input  logic                    s_axi_rready [NUM_MASTERS],

            // Slave Interfaces - Write Address Channel (AW)
            output logic [ADDR_WIDTH-1:0]   m_axi_awaddr  [NUM_SLAVES],
            output logic [ID_WIDTH-1:0]     m_axi_awid    [NUM_SLAVES],
            output logic [7:0]              m_axi_awlen   [NUM_SLAVES],
            output logic [2:0]              m_axi_awsize  [NUM_SLAVES],
            output logic [1:0]              m_axi_awburst [NUM_SLAVES],
            output logic                    m_axi_awlock  [NUM_SLAVES],
            output logic [3:0]              m_axi_awcache [NUM_SLAVES],
            output logic [2:0]              m_axi_awprot  [NUM_SLAVES],
            output logic                    m_axi_awvalid [NUM_SLAVES],
            input  logic                    m_axi_awready [NUM_SLAVES],

            // Slave Interfaces - Write Data Channel (W)
            output logic [DATA_WIDTH-1:0]   m_axi_wdata  [NUM_SLAVES],
            output logic [STRB_WIDTH-1:0]   m_axi_wstrb  [NUM_SLAVES],
            output logic                    m_axi_wlast  [NUM_SLAVES],
            output logic                    m_axi_wvalid [NUM_SLAVES],
            input  logic                    m_axi_wready [NUM_SLAVES],

            // Slave Interfaces - Write Response Channel (B)
            input  logic [ID_WIDTH-1:0]     m_axi_bid    [NUM_SLAVES],
            input  logic [1:0]              m_axi_bresp  [NUM_SLAVES],
            input  logic                    m_axi_bvalid [NUM_SLAVES],
            output logic                    m_axi_bready [NUM_SLAVES],

            // Slave Interfaces - Read Address Channel (AR)
            output logic [ADDR_WIDTH-1:0]   m_axi_araddr  [NUM_SLAVES],
            output logic [ID_WIDTH-1:0]     m_axi_arid    [NUM_SLAVES],
            output logic [7:0]              m_axi_arlen   [NUM_SLAVES],
            output logic [2:0]              m_axi_arsize  [NUM_SLAVES],
            output logic [1:0]              m_axi_arburst [NUM_SLAVES],
            output logic                    m_axi_arlock  [NUM_SLAVES],
            output logic [3:0]              m_axi_arcache [NUM_SLAVES],
            output logic [2:0]              m_axi_arprot  [NUM_SLAVES],
            output logic                    m_axi_arvalid [NUM_SLAVES],
            input  logic                    m_axi_arready [NUM_SLAVES],

            // Slave Interfaces - Read Data Channel (R)
            input  logic [DATA_WIDTH-1:0]   m_axi_rdata  [NUM_SLAVES],
            input  logic [ID_WIDTH-1:0]     m_axi_rid    [NUM_SLAVES],
            input  logic [1:0]              m_axi_rresp  [NUM_SLAVES],
            input  logic                    m_axi_rlast  [NUM_SLAVES],
            input  logic                    m_axi_rvalid [NUM_SLAVES],
            output logic                    m_axi_rready [NUM_SLAVES]
        '''
        self.ports.add_port_string(port_str)

    def generate_header_comment(self):
        """Generate Bridge-specific header comment"""
        self.comment("==============================================================================")
        self.comment(f"Module: {self.module_str}")
        self.comment("Project: Bridge - AXI4 Full Crossbar Generator")
        self.comment("==============================================================================")
        self.comment(f"Description: AXI4 {self.cfg.num_masters}×{self.cfg.num_slaves} Full Crossbar")
        self.comment("")
        self.comment("Bridge: Connecting masters and slaves across the divide")
        self.comment("")
        self.comment("Generated by: bridge_generator.py (framework version)")
        self.comment("Configuration:")
        self.comment(f"  - Masters: {self.cfg.num_masters}")
        self.comment(f"  - Slaves: {self.cfg.num_slaves}")
        self.comment(f"  - Data Width: {self.cfg.data_width} bits")
        self.comment(f"  - Address Width: {self.cfg.addr_width} bits")
        self.comment(f"  - ID Width: {self.cfg.id_width} bits")
        self.comment("")
        self.comment("Features:")
        self.comment("  - Full 5-channel AXI4 protocol (AW, W, B, AR, R)")
        self.comment("  - Out-of-order transaction support (ID-based routing)")
        self.comment("  - Separate read/write arbitration (no head-of-line blocking)")
        self.comment("  - Burst transfer optimization (grant locking until xlast)")
        self.comment("")
        self.comment("==============================================================================")
        self.instruction("")

    def generate_address_decode(self):
        """
        Generate address range decode logic

        KEY DIFFERENCE from Delta:
        - Delta: Direct TDEST decode (tdest is slave ID)
        - Bridge: Address range checking (like APB but for 2 channels: AW, AR)
        """
        self.comment("==========================================================================")
        self.comment("Write Address Decode (AW channel)")
        self.comment("==========================================================================")
        self.comment("Check each master's AWADDR against all slave address ranges")
        self.comment("Similar to APB crossbar but separate decode for write address channel")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] aw_request_matrix [NUM_SLAVES];")
        self.instruction("")

        self.instruction("always_comb begin")
        self.instruction("    // Initialize all write address requests to zero")
        self.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("        aw_request_matrix[s] = '0;")
        self.instruction("    end")
        self.instruction("")
        self.instruction("    // Decode AWADDR to slave for each master")
        self.instruction("    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("        if (s_axi_awvalid[m]) begin")

        # Generate address range checks for each slave
        for slave_idx, slave_info in self.cfg.address_map.items():
            base = slave_info['base']
            size = slave_info['size']
            name = slave_info.get('name', f'Slave{slave_idx}')
            end = base + size

            self.instruction(f"            // Slave {slave_idx}: {name} (0x{base:08X} - 0x{end-1:08X})")
            self.instruction(f"            if (s_axi_awaddr[m] >= {self.cfg.addr_width}'h{base:X} &&")
            self.instruction(f"                s_axi_awaddr[m] < {self.cfg.addr_width}'h{end:X})")
            self.instruction(f"                aw_request_matrix[{slave_idx}][m] = 1'b1;")
            self.instruction("")

        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

        # Similar decode for AR channel
        self.comment("==========================================================================")
        self.comment("Read Address Decode (AR channel)")
        self.comment("==========================================================================")
        self.comment("Separate decode for read address channel (independent from writes)")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] ar_request_matrix [NUM_SLAVES];")
        self.instruction("")

        self.instruction("always_comb begin")
        self.instruction("    // Initialize all read address requests to zero")
        self.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("        ar_request_matrix[s] = '0;")
        self.instruction("    end")
        self.instruction("")
        self.instruction("    // Decode ARADDR to slave for each master")
        self.instruction("    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("        if (s_axi_arvalid[m]) begin")

        for slave_idx, slave_info in self.cfg.address_map.items():
            base = slave_info['base']
            size = slave_info['size']
            name = slave_info.get('name', f'Slave{slave_idx}')
            end = base + size

            self.instruction(f"            // Slave {slave_idx}: {name} (0x{base:08X} - 0x{end-1:08X})")
            self.instruction(f"            if (s_axi_araddr[m] >= {self.cfg.addr_width}'h{base:X} &&")
            self.instruction(f"                s_axi_araddr[m] < {self.cfg.addr_width}'h{end:X})")
            self.instruction(f"                ar_request_matrix[{slave_idx}][m] = 1'b1;")
            self.instruction("")

        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

    def generate_arbiter_skeleton(self):
        """
        Generate placeholder for arbiter logic

        FULL IMPLEMENTATION NEEDED:
        - 5 separate arbiters per slave (AW, W, B, AR, R)
        - W channel locked to AW grant
        - B/R channels routed by ID (need transaction tables)
        - Burst locking (grant held until xlast)
        """
        self.comment("==========================================================================")
        self.comment("Per-Slave Arbitration (SKELETON - NEEDS FULL IMPLEMENTATION)")
        self.comment("==========================================================================")
        self.comment("TODO: Implement 5 separate arbiters per slave:")
        self.comment("  1. AW arbiter - Write address channel")
        self.comment("  2. W arbiter  - Write data channel (locked to AW grant)")
        self.comment("  3. B demux    - Write response channel (ID-based routing)")
        self.comment("  4. AR arbiter - Read address channel")
        self.comment("  5. R demux    - Read data channel (ID-based routing)")
        self.comment("")
        self.comment("KEY DIFFERENCES from Delta (AXIS):")
        self.comment("  - Delta: 1 arbiter per slave (simple)")
        self.comment("  - Bridge: 5 arbiters per slave (5× complexity)")
        self.comment("  - Bridge needs ID tables for B/R response routing")
        self.comment("  - Bridge needs W channel locking to AW grant")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("// Placeholder: Grant matrices for each channel")
        self.instruction("logic [NUM_MASTERS-1:0] aw_grant_matrix [NUM_SLAVES];")
        self.instruction("logic [NUM_MASTERS-1:0] ar_grant_matrix [NUM_SLAVES];")
        self.instruction("")

        self.instruction("// TODO: Implement full arbitration logic")
        self.instruction("// TODO: Implement ID tracking tables")
        self.instruction("// TODO: Implement response demux logic")
        self.instruction("")

    def verilog(self, file_path):
        """Generate complete RTL (main entry point)"""
        # Generate header comment
        self.generate_header_comment()

        # Generate logic sections
        self.generate_address_decode()
        self.generate_arbiter_skeleton()

        # Module framework handles module header/footer
        self.start()  # Auto-generates module header with ports/params
        self.end()    # Auto-generates endmodule

        # Write to file
        self.write(file_path, f'{self.module_name}.sv')


def main():
    parser = argparse.ArgumentParser(
        description="Bridge: AXI4 Full Crossbar Generator (Framework Version)",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )

    parser.add_argument("--masters", type=int, required=True, help="Number of master interfaces")
    parser.add_argument("--slaves", type=int, required=True, help="Number of slave interfaces")
    parser.add_argument("--data-width", type=int, default=512, help="Data bus width in bits")
    parser.add_argument("--addr-width", type=int, default=64, help="Address bus width in bits")
    parser.add_argument("--id-width", type=int, default=4, help="Transaction ID width in bits")
    parser.add_argument("--output-dir", type=str, default="../rtl", help="Output directory")
    parser.add_argument("--no-pipeline", action="store_true", help="Disable output registers")
    parser.add_argument("--no-counters", action="store_true", help="Disable performance counters")

    args = parser.parse_args()

    # Simple default address map (TODO: make configurable from file)
    address_map = {}
    base_addr = 0x00000000
    size_per_slave = 0x10000000  # 256MB per slave

    for s in range(args.slaves):
        address_map[s] = {
            'base': base_addr,
            'size': size_per_slave,
            'name': f'Slave{s}'
        }
        base_addr += size_per_slave

    config = BridgeConfig(
        num_masters=args.masters,
        num_slaves=args.slaves,
        data_width=args.data_width,
        addr_width=args.addr_width,
        id_width=args.id_width,
        address_map=address_map,
        pipeline_outputs=not args.no_pipeline,
        enable_counters=not args.no_counters
    )

    os.makedirs(args.output_dir, exist_ok=True)

    generator = BridgeFlatCrossbar(config)
    generator.verilog(args.output_dir)
    print(f"✓ Generated skeleton: {args.output_dir}/bridge_axi4_flat_{args.masters}x{args.slaves}.sv")
    print(f"")
    print(f"⚠ NOTE: This is a SKELETON implementation demonstrating framework usage.")
    print(f"  Full implementation requires:")
    print(f"  - 5 arbiters per slave (AW, W, B, AR, R)")
    print(f"  - ID tracking tables for out-of-order support")
    print(f"  - Response demux logic (B, R channels)")
    print(f"  - Burst handling with grant locking")
    print(f"")
    print(f"{'='*70}")
    print(f"✓ Bridge skeleton generation complete (framework version)!")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
