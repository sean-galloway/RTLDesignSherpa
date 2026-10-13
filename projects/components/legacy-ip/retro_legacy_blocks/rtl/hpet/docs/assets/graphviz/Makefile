# ==============================================================================
# Graphviz Diagram Makefile - HPET Module
# ==============================================================================

# Graphviz dot command
DOT = dot

# Source files
SOURCES = hpet_architecture.gv

# Generated files
PNGS = $(SOURCES:.gv=.png)
SVGS = $(SOURCES:.gv=.svg)

# ==============================================================================
# Targets
# ==============================================================================

all: $(PNGS) ## Generate all PNG diagrams (default)

%.png: %.gv
	@echo "Generating $@ from $<..."
	$(DOT) -Tpng $< -o $@

%.svg: %.gv
	@echo "Generating $@ from $<..."
	$(DOT) -Tsvg $< -o $@

svg: $(SVGS) ## Generate all SVG diagrams

full: all svg ## Generate all PNG and SVG diagrams

clean: ## Remove all generated files
	@echo "Cleaning generated PNG and SVG files..."
	rm -f $(PNGS) $(SVGS)

rebuild: clean all ## Clean and regenerate all diagrams

.PHONY: all svg full clean rebuild

# ==============================================================================
# Help
# ==============================================================================

help: ## Show this help message
	@echo "HPET Graphviz Diagram Makefile"
	@echo ""
	@echo "Targets:"
	@grep -h -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  %-12s %s\n", $$1, $$2}'
	@echo ""
	@echo "Source files:"
	@for file in $(SOURCES); do echo "  - $$file"; done
	@echo ""

.PHONY: help
