# ==============================================================================
# Graphviz Diagram Makefile - HPET Specification
# ==============================================================================

# Optional: Use common.mk for helper functions (print_*, etc.)
# But graphviz Makefiles are self-contained and don't need pytest/clean infrastructure
-include $(REPO_ROOT)/makefiles/common.mk

# Graphviz dot command
DOT = dot

# Source files (auto-detect .dot files)
SOURCES = $(wildcard *.dot)

# Generated files
PNGS = $(SOURCES:.dot=.png)
SVGS = $(SOURCES:.dot=.svg)

# ==============================================================================
# Targets
# ==============================================================================

all: $(PNGS) ## Generate all PNG diagrams (default)

%.png: %.dot
	@echo "$(BLUE)Generating $@ from $<...$(RESET)"
	$(DOT) -Tpng $< -o $@

%.svg: %.dot
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
	@echo "$(BOLD)HPET Graphviz Diagram Makefile$(RESET)"
	@echo ""
	@echo "$(GREEN)Targets:$(RESET)"
	@/bin/sh -c "grep -h -E '^[a-zA-Z_-]+:.*?## .*\$$' $(MAKEFILE_LIST) | sed -E 's/^([a-zA-Z_-]+):.*## (.*)\$$/\1@@@\2/' | awk -F'@@@' '{printf \"  %-12s %s\\n\", \$$1, \$$2}'"
	@echo ""
	@echo "$(GREEN)Source files:$(RESET)"
	@for file in $(SOURCES); do echo "  - $$file"; done
	@echo ""

.PHONY: help
