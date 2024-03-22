---
title: Python Scripts
date: 2024-02-15
type: index
layout: docs
categories: ["Python", "Python Script"]
---

This area contains all of the descriptions of the Python scripts. If you only want to know how to run the four main scripts, check out the [Cheat Sheet](./cheat_sheet)

If one wants to look further into the main scripts, follow these links:

- [Test List Creator](list_test_wrap)

- [Run Lint](lint_wrap)

- [Run Tests](run_test_wrap)

- [Generate Verilog for some adders and multipliers](math_generate)

- [Generate Verilog for Hamming encoders and decoders](ecc_generate)

- [VCD to Wavedrom 2](vcd2wavedrom2)

## Primary Use Classes

These are the main workhorse classes:

- [Lint](lint)

- [TestList](list_test)

- [RunTest](run_test)

- [REMatcher](REMatcher)

## Main Math Classes

These are the main instances of the different math classes created in Python to generate the underlying system verilog.

- [Brent Kung Adder](brent_kung_adder)

- [Dadda Multiplier](dadda_multiplier)

- [Wallace Multiplier](wallace_multiplier)

### These are the primary classes involved in creating System Verilog

- [Overview](verilog_class_overview)

- [Module](module)

- [Signal](signal)

- [Parameter](param)

- [Verilog Parser](verilog_parser)

### These are the final sub-blocks and subroutines that create the System Verilog

- [Bit-wise PG](bitwise_pg_logic)

- [PG](pg)

- [Black](black)

- [Gray](gray)

- [Group PG](group_pg_logic)

- [Multiplier Mixin](multiplier_mixin)

- [Utils](utils)

- [Sum](sum_logic)

---
