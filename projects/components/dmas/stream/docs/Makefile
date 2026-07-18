# STREAM Documentation Makefile
# Build the STREAM Micro-Architecture Specification

# Configuration
VERSION ?= 0.90
SPEC_DIR := stream_spec
OUTPUT_BASE := STREAM_Specification_v$(VERSION)
REPO_ROOT := $(shell cd ../../../.. && pwd)

# Tools
PYTHON := python3
MD_TO_DOCX := $(REPO_ROOT)/bin/md_to_docx.py

# Output files
DOCX := $(OUTPUT_BASE).docx
PDF := $(OUTPUT_BASE).pdf

# Default target
.PHONY: all
all: pdf

# Build PDF (and DOCX)
.PHONY: pdf
pdf:
	@echo "============================================================"
	@echo " Building STREAM Micro-Architecture Specification v$(VERSION)"
	@echo "============================================================"
	cd $(SPEC_DIR) && $(PYTHON) $(MD_TO_DOCX) \
		stream_index.md ../$(DOCX) \
		--expand-index --pdf --pagebreak --toc --number-sections \
		--skip-index-content --narrow-margins \
		--title-page title.md \
		--style stream_styles.yaml \
		--assets-dir assets/images \
		--assets-dir assets/mermaid \
		--assets-dir assets/wavedrom
	@echo ""
	@echo "Generated: $(DOCX)"
	@echo "Generated: $(PDF)"

# Build DOCX only (faster, no PDF conversion)
.PHONY: docx
docx:
	@echo "Building DOCX only..."
	cd $(SPEC_DIR) && $(PYTHON) $(MD_TO_DOCX) \
		stream_index.md ../$(DOCX) \
		--expand-index --pagebreak --toc --number-sections \
		--skip-index-content --narrow-margins \
		--title-page title.md \
		--style stream_styles.yaml \
		--assets-dir assets/images \
		--assets-dir assets/mermaid \
		--assets-dir assets/wavedrom
	@echo "Generated: $(DOCX)"

# Clean generated files
.PHONY: clean
clean:
	rm -f $(DOCX) $(PDF)
	rm -f STREAM_Specification_v*.docx STREAM_Specification_v*.pdf
	@echo "Cleaned generated files"

# Help
.PHONY: help
help:
	@echo "STREAM Documentation Build System"
	@echo ""
	@echo "Targets:"
	@echo "  all      - Build PDF (default)"
	@echo "  pdf      - Build DOCX and PDF"
	@echo "  docx     - Build DOCX only (faster)"
	@echo "  clean    - Remove generated files"
	@echo "  help     - Show this help"
	@echo ""
	@echo "Variables:"
	@echo "  VERSION  - Document version (default: $(VERSION))"
	@echo ""
	@echo "Examples:"
	@echo "  make                    # Build v$(VERSION) PDF"
	@echo "  make VERSION=1.0 pdf   # Build v1.0 PDF"
	@echo "  make docx              # Build DOCX only"
