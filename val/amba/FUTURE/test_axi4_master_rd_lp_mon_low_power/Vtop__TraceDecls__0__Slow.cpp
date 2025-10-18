// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Tracing declarations
#include "verilated_fst_c.h"


void Vtop___024root__traceDeclTypesSub0(VerilatedFst* tracep) {
    {
        const char* __VenumItemNames[]
        = {"PM_ACTIVE", "PM_IDLE", "PM_SLEEP_ENTRY", 
                                "PM_SLEEP", "PM_WAKE_UP", 
                                "PM_VF_SWITCH", "PM_ERROR"};
        const char* __VenumItemValues[]
        = {"0", "1", "10", "11", "100", "101", "110"};
        tracep->declDTypeEnum(1, "axi4_master_rd_lp_mon.pm_state_t", 7, 3, __VenumItemNames, __VenumItemValues);
    }
    {
        const char* __VenumItemNames[]
        = {"TRANS_IDLE", "TRANS_ADDR_PHASE", "TRANS_DATA_PHASE", 
                                "TRANS_COMPLETE", "TRANS_ERROR", 
                                "TRANS_ORPHANED"};
        const char* __VenumItemValues[]
        = {"0", "1", "10", "11", "100", "101"};
        tracep->declDTypeEnum(2, "monitor_pkg::transaction_state_t", 6, 3, __VenumItemNames, __VenumItemValues);
    }
    {
        const char* __VenumItemNames[]
        = {"AXI_TIMEOUT_CMD", "AXI_TIMEOUT_DATA", "AXI_TIMEOUT_RESP", 
                                "AXI_TIMEOUT_HANDSHAKE", 
                                "AXI_TIMEOUT_BURST", 
                                "AXI_TIMEOUT_EXCLUSIVE", 
                                "AXI_TIMEOUT_RESERVED_6", 
                                "AXI_TIMEOUT_RESERVED_7", 
                                "AXI_TIMEOUT_RESERVED_8", 
                                "AXI_TIMEOUT_RESERVED_9", 
                                "AXI_TIMEOUT_RESERVED_A", 
                                "AXI_TIMEOUT_RESERVED_B", 
                                "AXI_TIMEOUT_RESERVED_C", 
                                "AXI_TIMEOUT_RESERVED_D", 
                                "AXI_TIMEOUT_RESERVED_E", 
                                "AXI_TIMEOUT_USER_DEFINED"};
        const char* __VenumItemValues[]
        = {"0", "1", "10", "11", "100", "101", "110", 
                                "111", "1000", "1001", 
                                "1010", "1011", "1100", 
                                "1101", "1110", "1111"};
        tracep->declDTypeEnum(3, "monitor_pkg::axi_timeout_code_t", 16, 4, __VenumItemNames, __VenumItemValues);
    }
    {
        const char* __VenumItemNames[]
        = {"AXI_COMPL_TRANS_COMPLETE", "AXI_COMPL_READ_COMPLETE", 
                                "AXI_COMPL_WRITE_COMPLETE", 
                                "AXI_COMPL_BURST_COMPLETE", 
                                "AXI_COMPL_EXCLUSIVE_OK", 
                                "AXI_COMPL_EXCLUSIVE_FAIL", 
                                "AXI_COMPL_ATOMIC_OK", 
                                "AXI_COMPL_ATOMIC_FAIL", 
                                "AXI_COMPL_RESERVED_8", 
                                "AXI_COMPL_RESERVED_9", 
                                "AXI_COMPL_RESERVED_A", 
                                "AXI_COMPL_RESERVED_B", 
                                "AXI_COMPL_RESERVED_C", 
                                "AXI_COMPL_RESERVED_D", 
                                "AXI_COMPL_RESERVED_E", 
                                "AXI_COMPL_USER_DEFINED"};
        const char* __VenumItemValues[]
        = {"0", "1", "10", "11", "100", "101", "110", 
                                "111", "1000", "1001", 
                                "1010", "1011", "1100", 
                                "1101", "1110", "1111"};
        tracep->declDTypeEnum(4, "monitor_pkg::axi_completion_code_t", 16, 4, __VenumItemNames, __VenumItemValues);
    }
    {
        const char* __VenumItemNames[]
        = {"AXI_ERR_RESP_SLVERR", "AXI_ERR_RESP_DECERR", 
                                "AXI_ERR_DATA_ORPHAN", 
                                "AXI_ERR_RESP_ORPHAN", 
                                "AXI_ERR_PROTOCOL", 
                                "AXI_ERR_BURST_LENGTH", 
                                "AXI_ERR_BURST_SIZE", 
                                "AXI_ERR_BURST_TYPE", 
                                "AXI_ERR_ID_COLLISION", 
                                "AXI_ERR_WRITE_BEFORE_ADDR", 
                                "AXI_ERR_RESP_BEFORE_DATA", 
                                "AXI_ERR_LAST_MISSING", 
                                "AXI_ERR_STROBE_ERROR", 
                                "AXI_ERR_RESERVED_D", 
                                "AXI_ERR_RESERVED_E", 
                                "AXI_ERR_USER_DEFINED"};
        const char* __VenumItemValues[]
        = {"0", "1", "10", "11", "100", "101", "110", 
                                "111", "1000", "1001", 
                                "1010", "1011", "1100", 
                                "1101", "1110", "1111"};
        tracep->declDTypeEnum(5, "monitor_pkg::axi_error_code_t", 16, 4, __VenumItemNames, __VenumItemValues);
    }
}

void Vtop___024root__trace_decl_types(VerilatedFst* tracep) {
    Vtop___024root__traceDeclTypesSub0(tracep);
}
