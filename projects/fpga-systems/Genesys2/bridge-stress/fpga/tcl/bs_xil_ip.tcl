# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#==============================================================================
# bs_xil_ip.tcl -- create build-xil's AMD/Xilinx IP in the CURRENT project
#==============================================================================
#   bs_create_xil_ips <area>
#
#   bs_atg        AXI Traffic Generator, AXI4 Advanced mode: command RAMs,
#                 64-bit master, ID 2 (the atg port), 32-bit programming
#                 slave
#   bs_cdma       AXI Central DMA, simple mode, 64-bit, 256-beat bursts, DRE
#                 (unaligned copies)
#   bs_bram_ctrl  AXI BRAM Controller, 64-bit, ID 6 (the bram port), 64 KB,
#                 dual port: reads and writes proceed at once (single port,
#                 a DMA copying within it deadlocks: its read waits for the
#                 DMA to drain, the DMA's write waits for the read)
#   bs_bram       Block Memory Generator in BRAM-controller mode behind it
#   bs_pc_ddr     AXI Protocol Checker on the ddr link (128-bit, ID 6)
#   bs_pc_bram    AXI Protocol Checker on the bram link (64-bit, ID 6)
#
# Widths and IDs are the bridge_bs_xil.toml ports'; the tcl reads every
# CONFIG value back, because Vivado clamps or ignores a value it does not
# accept without an error.
#==============================================================================

# Set CONFIG values; `fixed` are values Vivado derives (not settable) that the
# build still depends on, so they are read back too.
proc bs_ip_set {name cfg {fixed {}}} {
    set_property -dict $cfg [get_ips $name]
    set bad 0
    set cfg [concat $cfg $fixed]
    foreach {k v} $cfg {
        set got [get_property $k [get_ips $name]]
        if {[string tolower $got] ne [string tolower $v]} {
            puts stderr "ERROR: $name $k = $got, asked for $v"
            incr bad
        }
    }
    if {$bad} { exit 1 }
}

proc bs_create_xil_ips {area} {
    # ---- traffic generator ---------------------------------------------------
    puts "\n--- bs_atg (axi_traffic_gen) ---"
    create_ip -name axi_traffic_gen -vendor xilinx.com -library ip -module_name bs_atg
    bs_ip_set bs_atg [list CONFIG.C_ATG_MODE {AXI4} CONFIG.C_ATG_MODE_L2 {Advanced} \
        CONFIG.C_M_AXI_DATA_WIDTH {64} CONFIG.C_M_AXI_THREAD_ID_WIDTH {2} \
        CONFIG.C_S_AXI_DATA_WIDTH {32} CONFIG.C_S_AXI_ID_WIDTH {1}] \
        [list CONFIG.C_M_AXI_ADDR_WIDTH {32}]

    # ---- DMA -------------------------------------------------------------------
    puts "\n--- bs_cdma (axi_cdma) ---"
    create_ip -name axi_cdma -vendor xilinx.com -library ip -module_name bs_cdma
    bs_ip_set bs_cdma [list CONFIG.C_INCLUDE_SG {0} CONFIG.C_M_AXI_DATA_WIDTH {64} \
        CONFIG.C_M_AXI_MAX_BURST_LEN {256} CONFIG.C_INCLUDE_DRE {1} \
        CONFIG.C_ADDR_WIDTH {32}]

    # ---- BRAM --------------------------------------------------------------------
    puts "\n--- bs_bram_ctrl (axi_bram_ctrl) + bs_bram (blk_mem_gen) ---"
    create_ip -name axi_bram_ctrl -vendor xilinx.com -library ip -module_name bs_bram_ctrl
    bs_ip_set bs_bram_ctrl [list CONFIG.PROTOCOL {AXI4} CONFIG.DATA_WIDTH {64} \
        CONFIG.ID_WIDTH {6} CONFIG.SINGLE_PORT_BRAM {0} CONFIG.ECC_TYPE {0} \
        CONFIG.MEM_DEPTH {8192} CONFIG.SUPPORTS_NARROW_BURST {1}]
    create_ip -name blk_mem_gen -vendor xilinx.com -library ip -module_name bs_bram
    bs_ip_set bs_bram [list CONFIG.Memory_Type {True_Dual_Port_RAM} \
        CONFIG.use_bram_block {BRAM_Controller} CONFIG.Enable_32bit_Address {true} \
        CONFIG.Use_Byte_Write_Enable {true} CONFIG.Byte_Size {8} \
        CONFIG.Write_Width_A {64} CONFIG.Read_Width_A {64} CONFIG.Write_Depth_A {8192} \
        CONFIG.Write_Width_B {64} CONFIG.Read_Width_B {64} \
        CONFIG.Register_PortA_Output_of_Memory_Primitives {false} CONFIG.Use_RSTA_Pin {true} \
        CONFIG.Register_PortB_Output_of_Memory_Primitives {false} CONFIG.Use_RSTB_Pin {true}]

    # ---- protocol checkers ---------------------------------------------------
    foreach {name dw} {bs_pc_ddr 128 bs_pc_bram 64} {
        puts "\n--- $name (axi_protocol_checker) ---"
        create_ip -name axi_protocol_checker -vendor xilinx.com -library ip -module_name $name
        bs_ip_set $name [list CONFIG.PROTOCOL {AXI4} CONFIG.READ_WRITE_MODE {READ_WRITE} \
            CONFIG.DATA_WIDTH $dw CONFIG.ID_WIDTH {6} CONFIG.ADDR_WIDTH {32} \
            CONFIG.MAX_RD_BURSTS {32} CONFIG.MAX_WR_BURSTS {32} \
            CONFIG.HAS_WSTRB {1} CONFIG.SUPPORTS_NARROW_BURST {1}]
    }

    set ips [get_ips {bs_atg bs_cdma bs_bram_ctrl bs_bram bs_pc_ddr bs_pc_bram}]
    generate_target {instantiation_template synthesis} $ips
    puts "\nbs_xil_ip: [llength $ips] IPs generated"
}
