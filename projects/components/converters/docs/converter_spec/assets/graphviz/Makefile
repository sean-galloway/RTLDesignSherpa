# Makefile for Converters Graphviz Diagrams
# Generates PNG images from .gv source files

# Graphviz dot command
DOT = dot

# Source files
SOURCES = axi_data_upsize.gv \
          axi_data_dnsize_single.gv \
          axi_data_dnsize_dual.gv \
          axi4_dwidth_converter_wr.gv \
          axi4_dwidth_converter_rd.gv \
          axi4_to_apb.gv \
          peakrdl_adapter.gv

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
	@echo "Converters Graphviz Diagram Makefile"
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
