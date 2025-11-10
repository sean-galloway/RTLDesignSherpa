// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hpet_regs_pkg
// Purpose: Hpet Regs Pkg module
//
// Documentation: projects/components/hpet_regs_pkg.sv/PRD.md
// Subsystem: hpet_regs_pkg.sv
//
// Author: sean galloway
// Created: 2025-10-18

package hpet_regs_pkg;

    localparam HPET_REGS_DATA_WIDTH = 32;
    localparam HPET_REGS_MIN_ADDR_WIDTH = 9;
    localparam HPET_REGS_SIZE = 'h200;
    localparam VENDOR_ID = 'h1;
    localparam REVISION_ID = 'h1;
    localparam NUM_TIMERS = 'h8;

    typedef struct {
        logic [4:0] next;
    } hpet_regs__HPET_ID__num_tim_cap__in_t;

    typedef struct {
        hpet_regs__HPET_ID__num_tim_cap__in_t num_tim_cap;
    } hpet_regs__HPET_ID__in_t;

    typedef struct {
        logic [7:0] next;
        logic hwset;
    } hpet_regs__HPET_STATUS__timer_int_status__in_t;

    typedef struct {
        hpet_regs__HPET_STATUS__timer_int_status__in_t timer_int_status;
    } hpet_regs__HPET_STATUS__in_t;

    typedef struct {
        logic [31:0] next;
    } hpet_regs__HPET_COUNTER_LO__counter_lo__in_t;

    typedef struct {
        hpet_regs__HPET_COUNTER_LO__counter_lo__in_t counter_lo;
    } hpet_regs__HPET_COUNTER_LO__in_t;

    typedef struct {
        logic [31:0] next;
    } hpet_regs__HPET_COUNTER_HI__counter_hi__in_t;

    typedef struct {
        hpet_regs__HPET_COUNTER_HI__counter_hi__in_t counter_hi;
    } hpet_regs__HPET_COUNTER_HI__in_t;

    typedef struct {
        hpet_regs__HPET_ID__in_t HPET_ID;
        hpet_regs__HPET_STATUS__in_t HPET_STATUS;
        hpet_regs__HPET_COUNTER_LO__in_t HPET_COUNTER_LO;
        hpet_regs__HPET_COUNTER_HI__in_t HPET_COUNTER_HI;
    } hpet_regs__in_t;

    typedef struct {
        logic value;
    } hpet_regs__HPET_CONFIG__hpet_enable__out_t;

    typedef struct {
        logic value;
    } hpet_regs__HPET_CONFIG__legacy_replacement__out_t;

    typedef struct {
        hpet_regs__HPET_CONFIG__hpet_enable__out_t hpet_enable;
        hpet_regs__HPET_CONFIG__legacy_replacement__out_t legacy_replacement;
    } hpet_regs__HPET_CONFIG__out_t;

    typedef struct {
        logic swmod;
    } hpet_regs__HPET_STATUS__timer_int_status__out_t;

    typedef struct {
        hpet_regs__HPET_STATUS__timer_int_status__out_t timer_int_status;
    } hpet_regs__HPET_STATUS__out_t;

    typedef struct {
        logic swmod;
    } hpet_regs__HPET_COUNTER_LO__counter_lo__out_t;

    typedef struct {
        hpet_regs__HPET_COUNTER_LO__counter_lo__out_t counter_lo;
    } hpet_regs__HPET_COUNTER_LO__out_t;

    typedef struct {
        logic swmod;
    } hpet_regs__HPET_COUNTER_HI__counter_hi__out_t;

    typedef struct {
        hpet_regs__HPET_COUNTER_HI__counter_hi__out_t counter_hi;
    } hpet_regs__HPET_COUNTER_HI__out_t;

    typedef struct {
        logic value;
    } hpet_regs__timer_regfile__TIMER_CONFIG__timer_enable__out_t;

    typedef struct {
        logic value;
    } hpet_regs__timer_regfile__TIMER_CONFIG__timer_int_enable__out_t;

    typedef struct {
        logic value;
    } hpet_regs__timer_regfile__TIMER_CONFIG__timer_type__out_t;

    typedef struct {
        logic value;
    } hpet_regs__timer_regfile__TIMER_CONFIG__timer_size__out_t;

    typedef struct {
        logic value;
    } hpet_regs__timer_regfile__TIMER_CONFIG__timer_value_set__out_t;

    typedef struct {
        hpet_regs__timer_regfile__TIMER_CONFIG__timer_enable__out_t timer_enable;
        hpet_regs__timer_regfile__TIMER_CONFIG__timer_int_enable__out_t timer_int_enable;
        hpet_regs__timer_regfile__TIMER_CONFIG__timer_type__out_t timer_type;
        hpet_regs__timer_regfile__TIMER_CONFIG__timer_size__out_t timer_size;
        hpet_regs__timer_regfile__TIMER_CONFIG__timer_value_set__out_t timer_value_set;
    } hpet_regs__timer_regfile__TIMER_CONFIG__out_t;

    typedef struct {
        logic [31:0] value;
    } hpet_regs__timer_regfile__TIMER_COMPARATOR_LO__timer_comp_lo__out_t;

    typedef struct {
        hpet_regs__timer_regfile__TIMER_COMPARATOR_LO__timer_comp_lo__out_t timer_comp_lo;
    } hpet_regs__timer_regfile__TIMER_COMPARATOR_LO__out_t;

    typedef struct {
        logic [31:0] value;
    } hpet_regs__timer_regfile__TIMER_COMPARATOR_HI__timer_comp_hi__out_t;

    typedef struct {
        hpet_regs__timer_regfile__TIMER_COMPARATOR_HI__timer_comp_hi__out_t timer_comp_hi;
    } hpet_regs__timer_regfile__TIMER_COMPARATOR_HI__out_t;

    typedef struct {
        hpet_regs__timer_regfile__TIMER_CONFIG__out_t TIMER_CONFIG;
        hpet_regs__timer_regfile__TIMER_COMPARATOR_LO__out_t TIMER_COMPARATOR_LO;
        hpet_regs__timer_regfile__TIMER_COMPARATOR_HI__out_t TIMER_COMPARATOR_HI;
    } hpet_regs__timer_regfile__out_t;

    typedef struct {
        hpet_regs__HPET_CONFIG__out_t HPET_CONFIG;
        hpet_regs__HPET_STATUS__out_t HPET_STATUS;
        hpet_regs__HPET_COUNTER_LO__out_t HPET_COUNTER_LO;
        hpet_regs__HPET_COUNTER_HI__out_t HPET_COUNTER_HI;
        hpet_regs__timer_regfile__out_t TIMER[8];
    } hpet_regs__out_t;
endpackage
