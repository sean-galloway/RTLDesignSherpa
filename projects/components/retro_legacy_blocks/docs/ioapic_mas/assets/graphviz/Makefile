# Makefile for generating IOAPIC diagram images from Graphviz sources
# Usage: make all

# Tools
DOT = dot
NEATO = neato

# Directories
PNG_DIR = ../png
SVG_DIR = ../svg

# Source files
DOT_SOURCES = delivery_fsm.dot
GV_SOURCES = apb_ioapic.gv indirect_access.gv

# Targets
PNG_TARGETS = $(DOT_SOURCES:.dot=.png) $(GV_SOURCES:.gv=.png)
SVG_TARGETS = $(DOT_SOURCES:.dot=.svg) $(GV_SOURCES:.gv=.svg)

.PHONY: all clean png svg

all: png svg

png: $(PNG_TARGETS)
	@mkdir -p $(PNG_DIR)
	@mv -f *.png $(PNG_DIR)/ 2>/dev/null || true
	@echo "PNG diagrams generated in $(PNG_DIR)/"

svg: $(SVG_TARGETS)
	@mkdir -p $(SVG_DIR)
	@mv -f *.svg $(SVG_DIR)/ 2>/dev/null || true
	@echo "SVG diagrams generated in $(SVG_DIR)/"

%.png: %.dot
	$(DOT) -Tpng $< -o $@

%.png: %.gv
	$(DOT) -Tpng $< -o $@

%.svg: %.dot
	$(DOT) -Tsvg $< -o $@

%.svg: %.gv
	$(DOT) -Tsvg $< -o $@

clean:
	rm -f *.png *.svg
	rm -f $(PNG_DIR)/*.png
	rm -f $(SVG_DIR)/*.svg

help:
	@echo "IOAPIC Graphviz Diagram Generator"
	@echo ""
	@echo "Targets:"
	@echo "  all   - Generate both PNG and SVG (default)"
	@echo "  png   - Generate PNG diagrams only"
	@echo "  svg   - Generate SVG diagrams only"
	@echo "  clean - Remove all generated images"
	@echo ""
	@echo "Source files:"
	@echo "  $(DOT_SOURCES)"
	@echo "  $(GV_SOURCES)"
