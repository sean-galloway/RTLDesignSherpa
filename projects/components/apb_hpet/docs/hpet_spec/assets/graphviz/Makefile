# Makefile for HPET Graphviz Diagrams
# Renders all .dot files to PNG and SVG formats

# Output formats
PNG_FORMAT = png
SVG_FORMAT = svg

# Find all .dot files
DOT_FILES = $(wildcard *.dot)

# Generate output filenames
PNG_FILES = $(DOT_FILES:.dot=.png)
SVG_FILES = $(DOT_FILES:.dot=.svg)

# Default target: build all PNGs
all: $(PNG_FILES)

# Build all SVGs
svg: $(SVG_FILES)

# Build both PNG and SVG
both: all svg

# Pattern rule for PNG generation
%.png: %.dot
	@echo "Rendering $< to PNG..."
	dot -T$(PNG_FORMAT) $< -o $@

# Pattern rule for SVG generation
%.svg: %.dot
	@echo "Rendering $< to SVG..."
	dot -T$(SVG_FORMAT) $< -o $@

# Individual targets for easy reference
software_init: software_init.png
oneshot_timer: oneshot_timer.png
periodic_timer: periodic_timer.png
interrupt_handling: interrupt_handling.png
timer_mode_switch: timer_mode_switch.png
multi_timer_concurrent: multi_timer_concurrent.png
cdc_handshake: cdc_handshake.png

# Clean generated files
clean:
	@echo "Cleaning generated files..."
	rm -f *.png *.svg

# Help target
help:
	@echo "HPET Graphviz Diagrams Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all                     - Build all PNG diagrams (default)"
	@echo "  svg                     - Build all SVG diagrams"
	@echo "  both                    - Build both PNG and SVG"
	@echo "  clean                   - Remove all generated files"
	@echo ""
	@echo "Individual diagram targets:"
	@echo "  software_init           - Software initialization flow"
	@echo "  oneshot_timer           - One-shot timer operation"
	@echo "  periodic_timer          - Periodic timer operation"
	@echo "  interrupt_handling      - Interrupt handling flow"
	@echo "  timer_mode_switch       - Timer mode switching"
	@echo "  multi_timer_concurrent  - Multi-timer concurrent operation"
	@echo "  cdc_handshake           - CDC handshake protocol"
	@echo ""
	@echo "Example usage:"
	@echo "  make all                - Build all PNG diagrams"
	@echo "  make svg                - Build all SVG diagrams"
	@echo "  make software_init      - Build specific diagram"

# Phony targets
.PHONY: all svg both clean help software_init oneshot_timer periodic_timer \
        interrupt_handling timer_mode_switch multi_timer_concurrent cdc_handshake
