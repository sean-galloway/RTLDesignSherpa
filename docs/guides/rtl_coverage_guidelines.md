# RTL Coverage Guidelines and Verilator Exclusion Techniques

## Coverage Targets

### Industry-Standard Targets for Production RTL

| Coverage Type | Target | Notes |
|---------------|--------|-------|
| Line/Statement | 95%+ | All executable lines should be exercised |
| Branch/Condition | 90%+ | All if/else, case branches taken |
| Toggle | 85-90% | All signals toggle 0→1 and 1→0 |
| FSM States | 100% | Every state must be entered |
| FSM Transitions | 100% | Every legal transition must be exercised |
| Functional Coverpoints | 100% | All defined scenarios must be hit |

### Why 75% Is Insufficient

- Uncovered code paths often hide corner-case bugs
- The gap between 75% and 95% typically contains error handling, edge cases, and rare conditions
- These are precisely the areas where silicon bugs are most likely to escape

### When Lower Coverage Is Acceptable

- Early development/prototyping phases
- With documented, justified exclusions for unreachable code
- Parameter-dependent dead code that cannot be exercised in a given configuration

---

## Verilator Coverage Exclusion Techniques

### Inline Pragmas

#### Single Line Exclusion
```systemverilog
assign debug_signal = some_value;  // verilator coverage_off
```

#### Block Exclusion
```systemverilog
/* verilator coverage_off */
// Code block that cannot be reached due to parameter settings
default: begin
    state <= IDLE;
    error <= 1'b1;
end
/* verilator coverage_on */
```

#### Toggle Coverage Exclusion Only
```systemverilog
logic unused_signal;  // verilator coverage_off_toggle
```

### Common Exclusion Scenarios

#### 1. Illegal Parameter Combinations
```systemverilog
generate
    if (MODE == "AXI" && WIDTH > 64) begin : g_axi_wide
        // Valid configuration - covered
        axi_wide_impl u_impl (...);
    end else if (MODE == "APB") begin : g_apb
        // Valid configuration - covered
        apb_impl u_impl (...);
    end else begin : g_invalid
        /* verilator coverage_off */
        // This parameter combination is not supported
        initial begin
            $error("Invalid configuration: MODE=%s, WIDTH=%0d", MODE, WIDTH);
        end
        /* verilator coverage_on */
    end
endgenerate
```

#### 2. Defensive Default Cases
```systemverilog
always_comb begin
    case (state)
        IDLE:   next_state = start ? ACTIVE : IDLE;
        ACTIVE: next_state = done  ? IDLE   : ACTIVE;
        /* verilator coverage_off */
        default: next_state = IDLE;  // Unreachable if FSM is correct
        /* verilator coverage_on */
    endcase
end
```

#### 3. Assertion-Only Logic
```systemverilog
/* verilator coverage_off */
// Synthesis-off debug/assertion logic
`ifdef SIMULATION
    always_ff @(posedge clk) begin
        if (error_condition) $error("Protocol violation detected");
    end
`endif
/* verilator coverage_on */
```

#### 4. Reset-Only Paths
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        /* verilator coverage_off */
        // Async reset path - toggle coverage not meaningful
        data_reg <= '0;
        /* verilator coverage_on */
    end else begin
        data_reg <= data_in;
    end
end
```

#### 5. Parameterized Width Dead Bits
```systemverilog
// When DATA_WIDTH < MAX_WIDTH, upper bits are unused
generate
    if (DATA_WIDTH < MAX_WIDTH) begin : g_unused_bits
        /* verilator coverage_off */
        // Upper bits are tied off and never toggle
        assign data_out[MAX_WIDTH-1:DATA_WIDTH] = '0;
        /* verilator coverage_on */
    end
endgenerate
```

---

## Verilator Coverage Commands

### Generating Coverage Data
```bash
# Compile with coverage enabled
verilator --cc --coverage design.sv

# Run simulation (generates coverage.dat)
./obj_dir/Vdesign

# Or specify output location
./obj_dir/Vdesign +verilator+coverage+file+mycoverage.dat
```

### Analyzing Coverage
```bash
# Generate annotated source files
verilator_coverage --annotate annotate_dir/ coverage.dat

# Generate summary report
verilator_coverage --summary coverage.dat

# Merge multiple coverage files
verilator_coverage --merge merged.dat run1.dat run2.dat run3.dat

# Write lcov format for external tools
verilator_coverage --write-info coverage.info coverage.dat
```

### Generating HTML Reports
```bash
# Using lcov/genhtml
verilator_coverage --write-info coverage.info coverage.dat
genhtml coverage.info --output-directory html_report
```

---

## CocoTB Integration

### Verilator Coverage with CocoTB Makefile
```makefile
VERILATOR_COVERAGE = 1
EXTRA_ARGS += --coverage

# After simulation
coverage:
    verilator_coverage --annotate annotate/ coverage.dat
    verilator_coverage --summary coverage.dat
```

### Functional Coverage with cocotb-coverage
```python
from cocotb_coverage.coverage import CoverPoint, CoverCross, coverage_db

@CoverPoint("top.transaction.size", 
            xf=lambda txn: txn.size, 
            bins=[1, 2, 4, 8, 16])
@CoverPoint("top.transaction.burst_type",
            xf=lambda txn: txn.burst,
            bins=["FIXED", "INCR", "WRAP"])
def sample_transaction(txn):
    pass

# Export coverage report
coverage_db.export_to_yaml("functional_coverage.yaml")
```

---

## Exclusion Documentation Best Practices

### Create an Exclusion Manifest

Maintain a file (e.g., `coverage_exclusions.md` or `coverage_waivers.yaml`) documenting each exclusion:

```yaml
exclusions:
  - file: src/axi_controller.sv
    line: 142-148
    type: branch
    reason: "Default case unreachable - all valid states enumerated"
    reviewer: "engineer_name"
    date: "2024-01-15"
    
  - file: src/fifo.sv
    line: 87
    type: toggle
    reason: "Parameterized - signal unused when DEPTH < 16"
    reviewer: "engineer_name"
    date: "2024-01-15"
```

### Exclusion Review Checklist

1. Is the exclusion truly unreachable, or just untested?
2. Can a test be written to cover this path instead?
3. Is the exclusion due to a design issue that should be fixed?
4. Has the exclusion been reviewed by someone other than the author?
5. Is the reason documented clearly for future maintainers?

---

## Summary

- Target 95%+ line coverage, 90%+ branch coverage for production RTL
- Use Verilator pragmas (`coverage_off`/`coverage_on`) to exclude genuinely unreachable code
- Document every exclusion with justification
- Combine RTL code coverage with functional coverage for complete verification
- Review exclusions periodically - conditions may change as design evolves
