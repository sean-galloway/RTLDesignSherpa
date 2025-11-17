# ==============================================================================
# Graphviz Diagram Makefile - Bridge Specification
# ==============================================================================

# Optional: Use common.mk for helper functions (print_*, etc.)
# But graphviz Makefiles are self-contained and don't need pytest/clean infrastructure
-include $(REPO_ROOT)/makefiles/common.mk

# Graphviz dot command
DOT = dot

# Source files
SOURCES = bridge_2x2.gv bridge_1x4.gv \
          master_adapter.gv slave_router.gv crossbar_core.gv \
          arbitration.gv id_management.gv width_conversion.gv \
          response_routing.gv error_handling.gv protocol_conversion_apb.gv

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
	@echo "$(BOLD)Bridge Graphviz Diagram Makefile$(RESET)"
	@echo ""
	@echo "$(GREEN)Targets:$(RESET)"
	@/bin/sh -c "grep -h -E '^[a-zA-Z_-]+:.*?## .*\$$' $(MAKEFILE_LIST) | sed -E 's/^([a-zA-Z_-]+):.*## (.*)\$$/\1@@@\2/' | awk -F'@@@' '{printf \"  %-12s %s\\n\", \$$1, \$$2}'"
	@echo ""
	@echo "$(GREEN)Source files:$(RESET)"
	@for file in $(SOURCES); do echo "  - $$file"; done
	@echo ""

.PHONY: help
