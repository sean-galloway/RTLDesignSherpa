# Makefile for Bridge Graphviz Diagrams
# Generates PNG images from .gv/.dot source files

# Graphviz dot command
DOT = dot

# Source files
SOURCES = bridge_2x2.gv bridge_1x4.gv

# Generated PNG files
PNGS = $(SOURCES:.gv=.png)

# Generated SVG files
SVGS = $(SOURCES:.gv=.svg)

# Default target: generate all PNGs
all: $(PNGS)

# Generate PNG from .gv source
%.png: %.gv
	@echo "Generating $@ from $<..."
	$(DOT) -Tpng $< -o $@

# Generate SVG from .gv source
%.svg: %.gv
	@echo "Generating $@ from $<..."
	$(DOT) -Tsvg $< -o $@

# Generate all SVGs
svg: $(SVGS)

# Generate all formats
full: all svg

# Clean generated files
clean:
	@echo "Cleaning generated PNG and SVG files..."
	rm -f $(PNGS) $(SVGS)

# Regenerate everything
rebuild: clean all

# Help target
help:
	@echo "Bridge Graphviz Diagram Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all     - Generate all PNG diagrams (default)"
	@echo "  svg     - Generate all SVG diagrams"
	@echo "  full    - Generate all PNG and SVG diagrams"
	@echo "  clean   - Remove all generated files"
	@echo "  rebuild - Clean and regenerate all diagrams"
	@echo "  help    - Show this help message"
	@echo ""
	@echo "Source files:"
	@for file in $(SOURCES); do echo "  - $$file"; done

.PHONY: all svg full clean rebuild help
