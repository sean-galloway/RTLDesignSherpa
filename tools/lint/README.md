# Lint Configuration

## Purpose
This directory contains lint configuration and waiver files for style-only lint warnings that don't affect functional correctness.

## Files

### verible_style_waivers.txt
Documentation of style rule waivers for Verible linter (for reference only).

**Current Waivers:**
- `parameter-name-style` - Repository uses UPPER_CASE for parameters and snake_case for localparams

## Implementation

The repository uses `--rules` flag directly in Makefiles for clarity:

```makefile
VERIBLE_FLAGS = --rules_config_search --rules=-parameter-name-style
```

This approach is preferred over waiver files because:
1. **Clear and explicit** - Rules are visible in the Makefile
2. **No file format confusion** - Direct flag usage
3. **Easy to modify** - Add more rules with comma separation

## Adding New Waivers

1. Run lint to identify the rule name
2. Add rule to waiver file with `-rule-name` format
3. Document why the waiver is needed
4. Re-run lint to verify

## Important Notes

- **Functional lint (Verilator) must still pass** - these are STYLE-ONLY waivers
- Waivers should be minimal and well-documented
- Consider if fixing the code is better than adding a waiver
- Waivers are project-wide - think carefully before adding

## Verible Documentation
https://github.com/chipsalliance/verible/tree/master/verilog/tools/lint
