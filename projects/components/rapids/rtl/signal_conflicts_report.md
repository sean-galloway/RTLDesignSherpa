# Signal Naming Conflict Report

**Generated:** audit_signal_naming_conflicts.py
**Conflicts Found:** 2

---

## Conflict #1: Prefix `desc` [HIGH]

### Internal Signals

- `desc_valid` - scheduler_group.sv:175
  ```systemverilog
  logic                        desc_valid;
  ```
- `desc_ready` - scheduler_group.sv:176
  ```systemverilog
  logic                        desc_ready;
  ```
- `desc_mon_valid` - scheduler_group.sv:198
  ```systemverilog
  logic                        desc_mon_valid;
  ```
- `desc_mon_ready` - scheduler_group.sv:199
  ```systemverilog
  logic                        desc_mon_ready;
  ```

### External Signals

- `desc_ar_valid` (output) - scheduler_group.sv:81
  ```systemverilog
  output logic                        desc_ar_valid,
  ```
- `desc_ar_ready` (input) - scheduler_group.sv:82
  ```systemverilog
  input  logic                        desc_ar_ready,
  ```
- `desc_r_valid` (input) - scheduler_group.sv:95
  ```systemverilog
  input  logic                        desc_r_valid,
  ```
- `desc_r_ready` (output) - scheduler_group.sv:96
  ```systemverilog
  output logic                        desc_r_ready,
  ```

### Impact

When using AXI factory with `prefix="desc_"`, the factory will find BOTH internal and external signals, causing initialization to fail.

### Recommended Solutions

1. **Rename internal signals:** `desc_valid` → `desc_valid_to_sched`
2. **Use explicit signal_map** parameter in factory call
3. **Test at higher integration level** where internal signals are hidden

---

## Conflict #2: Prefix `prog` [HIGH]

### Internal Signals

- `prog_valid` - scheduler_group.sv:188
  ```systemverilog
  logic                        prog_valid;
  ```
- `prog_ready` - scheduler_group.sv:189
  ```systemverilog
  logic                        prog_ready;
  ```
- `prog_mon_valid` - scheduler_group.sv:202
  ```systemverilog
  logic                        prog_mon_valid;
  ```
- `prog_mon_ready` - scheduler_group.sv:203
  ```systemverilog
  logic                        prog_mon_ready;
  ```

### External Signals

- `prog_aw_valid` (output) - scheduler_group.sv:103
  ```systemverilog
  output logic                        prog_aw_valid,
  ```
- `prog_aw_ready` (input) - scheduler_group.sv:104
  ```systemverilog
  input  logic                        prog_aw_ready,
  ```
- `prog_w_valid` (output) - scheduler_group.sv:117
  ```systemverilog
  output logic                        prog_w_valid,
  ```
- `prog_w_ready` (input) - scheduler_group.sv:118
  ```systemverilog
  input  logic                        prog_w_ready,
  ```
- `prog_b_valid` (input) - scheduler_group.sv:124
  ```systemverilog
  input  logic                        prog_b_valid,
  ```
- `prog_b_ready` (output) - scheduler_group.sv:125
  ```systemverilog
  output logic                        prog_b_ready,
  ```

### Impact

When using AXI factory with `prefix="prog_"`, the factory will find BOTH internal and external signals, causing initialization to fail.

### Recommended Solutions

1. **Rename internal signals:** `prog_valid` → `prog_valid_to_sched`
2. **Use explicit signal_map** parameter in factory call
3. **Test at higher integration level** where internal signals are hidden

---

