# ==============================================================================
# Graphviz Diagram Makefile - Converter Specification
# ==============================================================================

# Optional: Use common.mk for helper functions (print_*, etc.)
# But graphviz Makefiles are self-contained and don't need pytest/clean infrastructure
-include $(REPO_ROOT)/makefiles/common.mk

# Graphviz dot command
DOT = dot

# Source files
SOURCES = axi_data_upsize.gv \
          axi_data_dnsize_single.gv \
          axi_data_dnsize_dual.gv \
          axi4_dwidth_converter_wr.gv \
          axi4_dwidth_converter_rd.gv \
          axi4_to_apb.gv \
          peakrdl_adapter.gv \
          axi4_to_axil4.gv \
          axi4_to_axil4_rd.gv \
          axi4_to_axil4_wr.gv \
          axil4_to_axi4.gv \
          axil4_to_axi4_rd.gv \
          axil4_to_axi4_wr.gv \
          uart_axil_bridge.gv

# Generated files
PNGS = $(SOURCES:.gv=.png)
SVGS = $(SOURCES:.gv=.svg)

# ==============================================================================
# Targets
# ==============================================================================

all: $(PNGS) ## Generate all PNG diagrams (default)

%.png: %.gv
	@echo "$(BLUE)Generating $@ from $<...$(RESET)"
	$(DOT) -Tpng $< -o $@

%.svg: %.gv
	@echo "$(BLUE)Generating $@ from $<...$(RESET)"
	$(DOT) -Tsvg $< -o $@

svg: $(SVGS) ## Generate all SVG diagrams

full: all svg ## Generate all PNG and SVG diagrams

clean: ## Remove all generated files
	@echo "$(YELLOW)Cleaning generated PNG and SVG files...$(RESET)"
	rm -f $(PNGS) $(SVGS)

rebuild: clean all ## Clean and regenerate all diagrams

.PHONY: all svg full clean rebuild

# ==============================================================================
# Help (minimal - graphviz-specific)
# ==============================================================================

help: ## Show this help message
	@echo "$(BOLD)Converter Graphviz Diagram Makefile$(RESET)"
	@echo ""
	@echo "$(GREEN)Targets:$(RESET)"
	@/bin/sh -c "grep -h -E '^[a-zA-Z_-]+:.*?## .*\$$' $(MAKEFILE_LIST) | sed -E 's/^([a-zA-Z_-]+):.*## (.*)\$$/\1@@@\2/' | awk -F'@@@' '{printf \"  %-12s %s\\n\", \$$1, \$$2}'"
	@echo ""
	@echo "$(GREEN)Source files:$(RESET)"
	@for file in $(SOURCES); do echo "  - $$file"; done
	@echo ""

.PHONY: help
