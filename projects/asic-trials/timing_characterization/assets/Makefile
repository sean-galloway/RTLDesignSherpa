# Render every .mmd diagram in this directory to a matching .png.
# Requires `mmdc` (mermaid-cli) on PATH; install with:
#   npm install -g @mermaid-js/mermaid-cli
#
# puppeteer.json carries --no-sandbox so headless Chrome runs in CI/sandboxed envs.

MMD     := $(wildcard *.mmd)
PNG     := $(MMD:.mmd=.png)
WIDTH   ?= 1600
BG      ?= white

.PHONY: all clean

all: $(PNG)

%.png: %.mmd puppeteer.json
	mmdc -i $< -o $@ -b $(BG) -w $(WIDTH) -p puppeteer.json

clean:
	rm -f *.png
