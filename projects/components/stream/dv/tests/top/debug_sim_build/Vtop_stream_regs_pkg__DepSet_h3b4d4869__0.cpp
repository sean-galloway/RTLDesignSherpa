// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop_stream_regs_pkg.h"

std::string VL_TO_STRING(const Vtop_stream_regs___05FGLOBAL_STATUS___05FSYSTEM_IDLE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{next:" + VL_TO_STRING(obj.__PVT__next);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FGLOBAL_STATUS___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{SYSTEM_IDLE:" + VL_TO_STRING(obj.__PVT__SYSTEM_IDLE);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FCHANNEL_IDLE___05FCH_IDLE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{next:" + VL_TO_STRING(obj.__PVT__next);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FCHANNEL_IDLE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{CH_IDLE:" + VL_TO_STRING(obj.__PVT__CH_IDLE);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESC_ENGINE_IDLE___05FDESC_IDLE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{next:" + VL_TO_STRING(obj.__PVT__next);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESC_ENGINE_IDLE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{DESC_IDLE:" + VL_TO_STRING(obj.__PVT__DESC_IDLE);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHEDULER_IDLE___05FSCHED_IDLE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{next:" + VL_TO_STRING(obj.__PVT__next);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHEDULER_IDLE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{SCHED_IDLE:" + VL_TO_STRING(obj.__PVT__SCHED_IDLE);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FCH_STATE___05FSTATE___05FSTATE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{next:" + VL_TO_STRING(obj.__PVT__next);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FCH_STATE___05FSTATE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{STATE:" + VL_TO_STRING(obj.__PVT__STATE);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FCH_STATE___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{STATE:" + VL_TO_STRING(obj.__PVT__STATE);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05Fin_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{GLOBAL_STATUS:" + VL_TO_STRING(obj.__PVT__GLOBAL_STATUS);
        out += ", CHANNEL_IDLE:" + VL_TO_STRING(obj.__PVT__CHANNEL_IDLE);
        out += ", DESC_ENGINE_IDLE:" + VL_TO_STRING(obj.__PVT__DESC_ENGINE_IDLE);
        out += ", SCHEDULER_IDLE:" + VL_TO_STRING(obj.__PVT__SCHEDULER_IDLE);
        out += ", CH_STATE:" + VL_TO_STRING(obj.__PVT__CH_STATE);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FGLOBAL_CTRL___05FGLOBAL_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FGLOBAL_CTRL___05FGLOBAL_RST___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += ", swmod:" + VL_TO_STRING(obj.__PVT__swmod);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FGLOBAL_CTRL___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{GLOBAL_EN:" + VL_TO_STRING(obj.__PVT__GLOBAL_EN);
        out += ", GLOBAL_RST:" + VL_TO_STRING(obj.__PVT__GLOBAL_RST);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FCHANNEL_ENABLE___05FCH_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FCHANNEL_ENABLE___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{CH_EN:" + VL_TO_STRING(obj.__PVT__CH_EN);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FCHANNEL_RESET___05FCH_RST___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += ", swmod:" + VL_TO_STRING(obj.__PVT__swmod);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FCHANNEL_RESET___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{CH_RST:" + VL_TO_STRING(obj.__PVT__CH_RST);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHED_TIMEOUT_CYCLES___05FTIMEOUT_CYCLES___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHED_TIMEOUT_CYCLES___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{TIMEOUT_CYCLES:" + VL_TO_STRING(obj.__PVT__TIMEOUT_CYCLES);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHED_CONFIG___05FSCHED_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHED_CONFIG___05FTIMEOUT_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHED_CONFIG___05FERR_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHED_CONFIG___05FCOMPL_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHED_CONFIG___05FPERF_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FSCHED_CONFIG___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{SCHED_EN:" + VL_TO_STRING(obj.__PVT__SCHED_EN);
        out += ", TIMEOUT_EN:" + VL_TO_STRING(obj.__PVT__TIMEOUT_EN);
        out += ", ERR_EN:" + VL_TO_STRING(obj.__PVT__ERR_EN);
        out += ", COMPL_EN:" + VL_TO_STRING(obj.__PVT__COMPL_EN);
        out += ", PERF_EN:" + VL_TO_STRING(obj.__PVT__PERF_EN);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_CONFIG___05FDESCENG_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_CONFIG___05FPREFETCH_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_CONFIG___05FFIFO_THRESH___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_CONFIG___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{DESCENG_EN:" + VL_TO_STRING(obj.__PVT__DESCENG_EN);
        out += ", PREFETCH_EN:" + VL_TO_STRING(obj.__PVT__PREFETCH_EN);
        out += ", FIFO_THRESH:" + VL_TO_STRING(obj.__PVT__FIFO_THRESH);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_ADDR0_BASE___05FADDR0_BASE___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_ADDR0_BASE___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ADDR0_BASE:" + VL_TO_STRING(obj.__PVT__ADDR0_BASE);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_ADDR0_LIMIT___05FADDR0_LIMIT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_ADDR0_LIMIT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ADDR0_LIMIT:" + VL_TO_STRING(obj.__PVT__ADDR0_LIMIT);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_ADDR1_BASE___05FADDR1_BASE___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_ADDR1_BASE___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ADDR1_BASE:" + VL_TO_STRING(obj.__PVT__ADDR1_BASE);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_ADDR1_LIMIT___05FADDR1_LIMIT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDESCENG_ADDR1_LIMIT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ADDR1_LIMIT:" + VL_TO_STRING(obj.__PVT__ADDR1_LIMIT);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_ENABLE___05FMON_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_ENABLE___05FERR_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_ENABLE___05FCOMPL_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_ENABLE___05FTIMEOUT_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_ENABLE___05FPERF_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_ENABLE___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{MON_EN:" + VL_TO_STRING(obj.__PVT__MON_EN);
        out += ", ERR_EN:" + VL_TO_STRING(obj.__PVT__ERR_EN);
        out += ", COMPL_EN:" + VL_TO_STRING(obj.__PVT__COMPL_EN);
        out += ", TIMEOUT_EN:" + VL_TO_STRING(obj.__PVT__TIMEOUT_EN);
        out += ", PERF_EN:" + VL_TO_STRING(obj.__PVT__PERF_EN);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_TIMEOUT___05FTIMEOUT_CYCLES___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_TIMEOUT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{TIMEOUT_CYCLES:" + VL_TO_STRING(obj.__PVT__TIMEOUT_CYCLES);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_LATENCY_THRESH___05FLATENCY_THRESH___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_LATENCY_THRESH___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{LATENCY_THRESH:" + VL_TO_STRING(obj.__PVT__LATENCY_THRESH);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_PKT_MASK___05FPKT_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_PKT_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{PKT_MASK:" + VL_TO_STRING(obj.__PVT__PKT_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_ERR_CFG___05FERR_SELECT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_ERR_CFG___05FERR_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_ERR_CFG___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ERR_SELECT:" + VL_TO_STRING(obj.__PVT__ERR_SELECT);
        out += ", ERR_MASK:" + VL_TO_STRING(obj.__PVT__ERR_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_MASK1___05FTIMEOUT_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_MASK1___05FCOMPL_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_MASK1___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{TIMEOUT_MASK:" + VL_TO_STRING(obj.__PVT__TIMEOUT_MASK);
        out += ", COMPL_MASK:" + VL_TO_STRING(obj.__PVT__COMPL_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_MASK2___05FTHRESH_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_MASK2___05FPERF_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_MASK2___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{THRESH_MASK:" + VL_TO_STRING(obj.__PVT__THRESH_MASK);
        out += ", PERF_MASK:" + VL_TO_STRING(obj.__PVT__PERF_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_MASK3___05FADDR_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_MASK3___05FDEBUG_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FDAXMON_MASK3___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ADDR_MASK:" + VL_TO_STRING(obj.__PVT__ADDR_MASK);
        out += ", DEBUG_MASK:" + VL_TO_STRING(obj.__PVT__DEBUG_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_ENABLE___05FMON_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_ENABLE___05FERR_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_ENABLE___05FCOMPL_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_ENABLE___05FTIMEOUT_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_ENABLE___05FPERF_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_ENABLE___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{MON_EN:" + VL_TO_STRING(obj.__PVT__MON_EN);
        out += ", ERR_EN:" + VL_TO_STRING(obj.__PVT__ERR_EN);
        out += ", COMPL_EN:" + VL_TO_STRING(obj.__PVT__COMPL_EN);
        out += ", TIMEOUT_EN:" + VL_TO_STRING(obj.__PVT__TIMEOUT_EN);
        out += ", PERF_EN:" + VL_TO_STRING(obj.__PVT__PERF_EN);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_TIMEOUT___05FTIMEOUT_CYCLES___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_TIMEOUT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{TIMEOUT_CYCLES:" + VL_TO_STRING(obj.__PVT__TIMEOUT_CYCLES);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_LATENCY_THRESH___05FLATENCY_THRESH___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_LATENCY_THRESH___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{LATENCY_THRESH:" + VL_TO_STRING(obj.__PVT__LATENCY_THRESH);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_PKT_MASK___05FPKT_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_PKT_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{PKT_MASK:" + VL_TO_STRING(obj.__PVT__PKT_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_ERR_CFG___05FERR_SELECT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_ERR_CFG___05FERR_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_ERR_CFG___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ERR_SELECT:" + VL_TO_STRING(obj.__PVT__ERR_SELECT);
        out += ", ERR_MASK:" + VL_TO_STRING(obj.__PVT__ERR_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_MASK1___05FTIMEOUT_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_MASK1___05FCOMPL_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_MASK1___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{TIMEOUT_MASK:" + VL_TO_STRING(obj.__PVT__TIMEOUT_MASK);
        out += ", COMPL_MASK:" + VL_TO_STRING(obj.__PVT__COMPL_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_MASK2___05FTHRESH_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_MASK2___05FPERF_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_MASK2___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{THRESH_MASK:" + VL_TO_STRING(obj.__PVT__THRESH_MASK);
        out += ", PERF_MASK:" + VL_TO_STRING(obj.__PVT__PERF_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_MASK3___05FADDR_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_MASK3___05FDEBUG_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FRDMON_MASK3___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ADDR_MASK:" + VL_TO_STRING(obj.__PVT__ADDR_MASK);
        out += ", DEBUG_MASK:" + VL_TO_STRING(obj.__PVT__DEBUG_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_ENABLE___05FMON_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_ENABLE___05FERR_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_ENABLE___05FCOMPL_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_ENABLE___05FTIMEOUT_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_ENABLE___05FPERF_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_ENABLE___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{MON_EN:" + VL_TO_STRING(obj.__PVT__MON_EN);
        out += ", ERR_EN:" + VL_TO_STRING(obj.__PVT__ERR_EN);
        out += ", COMPL_EN:" + VL_TO_STRING(obj.__PVT__COMPL_EN);
        out += ", TIMEOUT_EN:" + VL_TO_STRING(obj.__PVT__TIMEOUT_EN);
        out += ", PERF_EN:" + VL_TO_STRING(obj.__PVT__PERF_EN);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_TIMEOUT___05FTIMEOUT_CYCLES___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_TIMEOUT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{TIMEOUT_CYCLES:" + VL_TO_STRING(obj.__PVT__TIMEOUT_CYCLES);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_LATENCY_THRESH___05FLATENCY_THRESH___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_LATENCY_THRESH___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{LATENCY_THRESH:" + VL_TO_STRING(obj.__PVT__LATENCY_THRESH);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_PKT_MASK___05FPKT_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_PKT_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{PKT_MASK:" + VL_TO_STRING(obj.__PVT__PKT_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_ERR_CFG___05FERR_SELECT___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_ERR_CFG___05FERR_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_ERR_CFG___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ERR_SELECT:" + VL_TO_STRING(obj.__PVT__ERR_SELECT);
        out += ", ERR_MASK:" + VL_TO_STRING(obj.__PVT__ERR_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_MASK1___05FTIMEOUT_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_MASK1___05FCOMPL_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_MASK1___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{TIMEOUT_MASK:" + VL_TO_STRING(obj.__PVT__TIMEOUT_MASK);
        out += ", COMPL_MASK:" + VL_TO_STRING(obj.__PVT__COMPL_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_MASK2___05FTHRESH_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_MASK2___05FPERF_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_MASK2___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{THRESH_MASK:" + VL_TO_STRING(obj.__PVT__THRESH_MASK);
        out += ", PERF_MASK:" + VL_TO_STRING(obj.__PVT__PERF_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_MASK3___05FADDR_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_MASK3___05FDEBUG_MASK___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FWRMON_MASK3___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{ADDR_MASK:" + VL_TO_STRING(obj.__PVT__ADDR_MASK);
        out += ", DEBUG_MASK:" + VL_TO_STRING(obj.__PVT__DEBUG_MASK);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FAXI_XFER_CONFIG___05FRD_XFER_BEATS___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FAXI_XFER_CONFIG___05FWR_XFER_BEATS___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FAXI_XFER_CONFIG___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{RD_XFER_BEATS:" + VL_TO_STRING(obj.__PVT__RD_XFER_BEATS);
        out += ", WR_XFER_BEATS:" + VL_TO_STRING(obj.__PVT__WR_XFER_BEATS);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FPERF_CONFIG___05FPERF_EN___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FPERF_CONFIG___05FPERF_MODE___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FPERF_CONFIG___05FPERF_CLEAR___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{value:" + VL_TO_STRING(obj.__PVT__value);
        out += ", swmod:" + VL_TO_STRING(obj.__PVT__swmod);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05FPERF_CONFIG___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{PERF_EN:" + VL_TO_STRING(obj.__PVT__PERF_EN);
        out += ", PERF_MODE:" + VL_TO_STRING(obj.__PVT__PERF_MODE);
        out += ", PERF_CLEAR:" + VL_TO_STRING(obj.__PVT__PERF_CLEAR);
        out += "}";
    return out;
}

std::string VL_TO_STRING(const Vtop_stream_regs___05Fout_t__struct__0& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+        Vtop_stream_regs_pkg::VL_TO_STRING\n"); );
    // Body
    std::string out;
    out += "'{GLOBAL_CTRL:" + VL_TO_STRING(obj.__PVT__GLOBAL_CTRL);
        out += ", CHANNEL_ENABLE:" + VL_TO_STRING(obj.__PVT__CHANNEL_ENABLE);
        out += ", CHANNEL_RESET:" + VL_TO_STRING(obj.__PVT__CHANNEL_RESET);
        out += ", SCHED_TIMEOUT_CYCLES:" + VL_TO_STRING(obj.__PVT__SCHED_TIMEOUT_CYCLES);
        out += ", SCHED_CONFIG:" + VL_TO_STRING(obj.__PVT__SCHED_CONFIG);
        out += ", DESCENG_CONFIG:" + VL_TO_STRING(obj.__PVT__DESCENG_CONFIG);
        out += ", DESCENG_ADDR0_BASE:" + VL_TO_STRING(obj.__PVT__DESCENG_ADDR0_BASE);
        out += ", DESCENG_ADDR0_LIMIT:" + VL_TO_STRING(obj.__PVT__DESCENG_ADDR0_LIMIT);
        out += ", DESCENG_ADDR1_BASE:" + VL_TO_STRING(obj.__PVT__DESCENG_ADDR1_BASE);
        out += ", DESCENG_ADDR1_LIMIT:" + VL_TO_STRING(obj.__PVT__DESCENG_ADDR1_LIMIT);
        out += ", DAXMON_ENABLE:" + VL_TO_STRING(obj.__PVT__DAXMON_ENABLE);
        out += ", DAXMON_TIMEOUT:" + VL_TO_STRING(obj.__PVT__DAXMON_TIMEOUT);
        out += ", DAXMON_LATENCY_THRESH:" + VL_TO_STRING(obj.__PVT__DAXMON_LATENCY_THRESH);
        out += ", DAXMON_PKT_MASK:" + VL_TO_STRING(obj.__PVT__DAXMON_PKT_MASK);
        out += ", DAXMON_ERR_CFG:" + VL_TO_STRING(obj.__PVT__DAXMON_ERR_CFG);
        out += ", DAXMON_MASK1:" + VL_TO_STRING(obj.__PVT__DAXMON_MASK1);
        out += ", DAXMON_MASK2:" + VL_TO_STRING(obj.__PVT__DAXMON_MASK2);
        out += ", DAXMON_MASK3:" + VL_TO_STRING(obj.__PVT__DAXMON_MASK3);
        out += ", RDMON_ENABLE:" + VL_TO_STRING(obj.__PVT__RDMON_ENABLE);
        out += ", RDMON_TIMEOUT:" + VL_TO_STRING(obj.__PVT__RDMON_TIMEOUT);
        out += ", RDMON_LATENCY_THRESH:" + VL_TO_STRING(obj.__PVT__RDMON_LATENCY_THRESH);
        out += ", RDMON_PKT_MASK:" + VL_TO_STRING(obj.__PVT__RDMON_PKT_MASK);
        out += ", RDMON_ERR_CFG:" + VL_TO_STRING(obj.__PVT__RDMON_ERR_CFG);
        out += ", RDMON_MASK1:" + VL_TO_STRING(obj.__PVT__RDMON_MASK1);
        out += ", RDMON_MASK2:" + VL_TO_STRING(obj.__PVT__RDMON_MASK2);
        out += ", RDMON_MASK3:" + VL_TO_STRING(obj.__PVT__RDMON_MASK3);
        out += ", WRMON_ENABLE:" + VL_TO_STRING(obj.__PVT__WRMON_ENABLE);
        out += ", WRMON_TIMEOUT:" + VL_TO_STRING(obj.__PVT__WRMON_TIMEOUT);
        out += ", WRMON_LATENCY_THRESH:" + VL_TO_STRING(obj.__PVT__WRMON_LATENCY_THRESH);
        out += ", WRMON_PKT_MASK:" + VL_TO_STRING(obj.__PVT__WRMON_PKT_MASK);
        out += ", WRMON_ERR_CFG:" + VL_TO_STRING(obj.__PVT__WRMON_ERR_CFG);
        out += ", WRMON_MASK1:" + VL_TO_STRING(obj.__PVT__WRMON_MASK1);
        out += ", WRMON_MASK2:" + VL_TO_STRING(obj.__PVT__WRMON_MASK2);
        out += ", WRMON_MASK3:" + VL_TO_STRING(obj.__PVT__WRMON_MASK3);
        out += ", AXI_XFER_CONFIG:" + VL_TO_STRING(obj.__PVT__AXI_XFER_CONFIG);
        out += ", PERF_CONFIG:" + VL_TO_STRING(obj.__PVT__PERF_CONFIG);
        out += "}";
    return out;
}
