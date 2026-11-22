// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: model_test.h (riscv-arch-test DUT model, falcon-suite RV32I cores)
// Purpose: The RVMODEL_* macros riscv-arch-test 3.x asks of a DUT.  The
//          reference build uses the suite's own spike plugin env
//          (vendor/riscv-arch-test/riscof-plugins/rv32/spike_simple/env),
//          which ends on a tohost write; this one ends on ECALL, the halt
//          every falcon-suite core implements (halt cause 1).  Both builds
//          link with the spike plugin's link.ld, so the two images differ
//          only in the halt sequence, as RISCOF's DUT and reference builds
//          do.  The signature is the memory between begin_signature and
//          end_signature after the halt.
//
// Documentation: vault/handbook/dv/riscv-arch-test.md
// Subsystem: riscv-ip/common-rv32i
//
// Author: sean galloway
// Created: 2026-11-22

#ifndef _COMPLIANCE_MODEL_H
#define _COMPLIANCE_MODEL_H

#if XLEN == 64
  #define ALIGNMENT 3
#else
  #define ALIGNMENT 2
#endif

// The core halts ON the ecall (it never retires past it); the loop only
// keeps a core that did not halt from running into the data section.
#define RVMODEL_HALT                                                    \
  .global rvmodel_halt; rvmodel_halt:                                   \
  ecall;                                                                \
  1: j 1b;

#define RVMODEL_BOOT

#define RVMODEL_DATA_BEGIN                                              \
  .align ALIGNMENT;                                                     \
  .global begin_signature; begin_signature:

#define RVMODEL_DATA_END                                                \
  .global end_signature; end_signature:

// No console on the falcon-suite TBs.
#define RVMODEL_IO_INIT
#define RVMODEL_IO_WRITE_STR(_R, _STR)
#define RVMODEL_IO_CHECK()
#define RVMODEL_IO_ASSERT_GPR_EQ(_S, _R, _I)
#define RVMODEL_IO_ASSERT_SFPR_EQ(_F, _R, _I)
#define RVMODEL_IO_ASSERT_DFPR_EQ(_D, _R, _I)

// No interrupt sources: the rv32i_m/I tests take none.
#define RVMODEL_SET_MSW_INT
#define RVMODEL_CLEAR_MSW_INT
#define RVMODEL_CLEAR_MTIMER_INT
#define RVMODEL_CLEAR_MEXT_INT

#endif // _COMPLIANCE_MODEL_H
