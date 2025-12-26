#!/usr/bin/env python3
"""
md_to_docx.py — Convert Markdown (single file or expanded index) to DOCX/PDF via Pandoc.

Features:
- --expand-index: parse an index.md and inline linked chapter .md files in order
- --skip-index-content: exclude index file content, only include linked chapters
- --title-page [path]: prepend a title page (auto if no path given)
- --assets-dir (repeatable): added to Pandoc --resource-path
- --pagebreak: insert page breaks between concatenated files
- --section-breaks: start each top-level section on a new page (PDF only)
- --toc: generate table of contents with clickable links (depth=3)
- --number-sections: add section numbering (1, 1.1, 1.1.1)
- PDF: hyperref enabled for clickable TOC, internal links, and PDF bookmarks
- Emoji mapping for PDF robustness
- Force a Unicode-friendly PDF engine (xelatex) by default
- Wavedrom .json "images": render to SVG (python-wavedrom or wavedrom-cli) or degrade to links
- Mermaid diagrams: ```mermaid blocks rendered to PNG via mmdc CLI
- Font controls for XeLaTeX/LuaLaTeX: --mainfont/--monofont/--sansfont/--mathfont

Required tools for diagram rendering:
- Mermaid: npm install -g @mermaid-js/mermaid-cli (provides 'mmdc')

Note on DOCX TOC: Word may require updating the TOC (Ctrl+A, F9) to populate entries.
"""

import argparse
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import date

# ---------------------------
# Config / Helpers
# ---------------------------

MD_LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+\.md)(#[^)]+)?\)", re.IGNORECASE)
IMG_JSON_RE = re.compile(r'!\[([^\]]*)\]\(([^)]+\.json)\)')
IMG_RE = re.compile(r'!\[([^\]]*)\]\(([^)]+)\)')
# Fenced code block pattern for mermaid diagrams
# Captures: (1) optional figure title line, (2) mermaid code content
MERMAID_BLOCK_RE = re.compile(
    r'(#{2,4}\s+(?:Figure\s+\d+[:\s]+)?[^\n]+\n+)?```mermaid\s*\n(.*?)\n```',
    re.DOTALL | re.IGNORECASE
)

EMOJI_MAP = {
    "✅": "✓",
    "❌": "✗",
    "➕": "+",
    "➖": "−",
    "⚠️": "⚠",
    "ℹ️": "ℹ",
    "🛠️": "🛠",
    "📌": "",
    "🚧": "",
}

def log(*a, **k):
    if not k.pop("_quiet", False):
        print(*a, **k, file=sys.stderr)

def read_text(p: pathlib.Path) -> str:
    return p.read_text(encoding="utf-8")

def write_text(p: pathlib.Path, s: str):
    p.write_text(s, encoding="utf-8")

def strip_or_map_emoji(s: str) -> str:
    for k, v in EMOJI_MAP.items():
        s = s.replace(k, v)
    return s

# ---- Mermaid handling ----

def render_mermaid_block(code: str, tmp_img_dir: pathlib.Path, idx: int, title: str = None, quiet: bool = False) -> str:
    """
    Render a Mermaid diagram code block to PNG.
    Returns markdown image reference or fallback code block.

    Note: PNG is used instead of SVG because SVG output from headless Chrome
    often has font/text rendering issues when fonts aren't installed in the
    headless environment.
    """
    out_png = tmp_img_dir / f"mermaid_{idx}.png"
    alt_text = title if title else f"Diagram {idx}"

    # Try mmdc CLI (mermaid-cli from npm)
    mmdc = shutil.which("mmdc")
    if mmdc:
        tmp_mmd = tmp_img_dir / f"mermaid_{idx}.mmd"
        write_text(tmp_mmd, code)

        # Create puppeteer config to disable sandbox (required on Ubuntu 23.10+)
        puppeteer_config = tmp_img_dir / "puppeteer-config.json"
        if not puppeteer_config.exists():
            write_text(puppeteer_config, '{"args": ["--no-sandbox", "--disable-setuid-sandbox"]}')

        try:
            # Use PNG output with high scale for quality, white background for better PDF embedding
            cmd = [mmdc, "-i", str(tmp_mmd), "-o", str(out_png), "-b", "white",
                   "-p", str(puppeteer_config), "-s", "2"]  # scale=2 for higher resolution
            if quiet:
                cmd.append("-q")
            subprocess.run(cmd, check=True, capture_output=True, timeout=30)
            if out_png.exists():
                if not quiet:
                    log(f"  Rendered mermaid_{idx}.png: {alt_text}")
                return f"![{alt_text}]({out_png.as_posix()})"
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
            if not quiet:
                log(f"  Warning: Mermaid render failed for block {idx}: {e}")

    # Fallback: keep as code block
    if not quiet:
        log(f"  Warning: mmdc not found, keeping mermaid block {idx} as code")
    return f"```\n{code}\n```"

def rewrite_mermaid_blocks(md_text: str, tmp_img_dir: pathlib.Path, quiet: bool = False) -> str:
    """Replace all ```mermaid blocks with rendered PNG images."""
    idx = [0]  # Use list to allow mutation in nested function

    def _sub(m):
        title_line = m.group(1)  # Optional figure title line (e.g., "### Figure 1: Title\n")
        code = m.group(2).strip()
        idx[0] += 1

        # Extract clean title from the heading line
        title = None
        if title_line:
            # Remove markdown heading markers and clean up
            title = re.sub(r'^#+\s*', '', title_line.strip())
            # Remove "Figure N:" prefix since Pandoc adds its own
            title = re.sub(r'^Figure\s+\d+[:\s]*', '', title)
            title = title.rstrip(':').strip()

        return render_mermaid_block(code, tmp_img_dir, idx[0], title, quiet)

    return MERMAID_BLOCK_RE.sub(_sub, md_text)

def collect_from_index(index_path: pathlib.Path, skip_index: bool = False) -> list[pathlib.Path]:
    """
    Scan the index markdown for links to .md files and return them in order.
    Keeps only links that resolve relative to the index folder.

    Args:
        index_path: Path to the index markdown file
        skip_index: If True, don't include the index file itself (only linked chapters)
    """
    root = index_path.parent
    content = read_text(index_path)
    links = []
    seen = set()

    # Inline comment include directive support:  <!-- include: path/to/file.md -->
    for inc in re.findall(r'<!--\s*include:\s*([^\s>]+\.md)\s*-->', content, flags=re.IGNORECASE):
        p = (root / inc).resolve()
        if p.exists() and p.suffix.lower() == ".md" and p not in seen:
            links.append(p); seen.add(p)

    for m in MD_LINK_RE.finditer(content):
        rel = m.group(2).strip()
        if "://" in rel or rel.startswith("#"):
            continue
        p = (root / rel).resolve()
        if p.suffix.lower() == ".md" and p.exists() and p not in seen:
            links.append(p); seen.add(p)

    # Only include index file if not skipping it
    if not skip_index:
        idx = index_path.resolve()
        if idx not in seen:
            links = [idx] + links
        else:
            links = [idx] + [p for p in links if p != idx]

    return links

def rewrite_image_paths_for_file(text: str, source_file: pathlib.Path) -> str:
    """
    Rewrite relative image paths in markdown text to absolute paths.
    This is necessary when concatenating markdown files from different directories.
    """
    def _sub(m):
        alt, path = m.group(1), m.group(2)
        # Skip absolute paths, URLs, and already processed paths
        if path.startswith('/') or '://' in path:
            return m.group(0)
        # Resolve relative path based on source file location
        abs_path = (source_file.parent / path).resolve()
        if abs_path.exists():
            return f"![{alt}]({abs_path.as_posix()})"
        # If file doesn't exist, keep original reference
        return m.group(0)
    return IMG_RE.sub(_sub, text)

def concat_markdown(files: list[pathlib.Path], pagebreak: bool) -> str:
    parts = []
    for i, f in enumerate(files):
        text = read_text(f).rstrip() + "\n"
        # Rewrite relative image paths to absolute paths
        text = rewrite_image_paths_for_file(text, f)
        parts.append(text)
        if pagebreak and i < len(files) - 1:
            parts.append('\n::: {.pagebreak}\n:::\n')
    return "\n".join(parts)

# ---- Wavedrom handling ----

def try_render_wavedrom_python(json_path: pathlib.Path) -> str | None:
    try:
        import wavedrom
        svg = wavedrom.render_file(str(json_path))  # returns SVG string in recent versions
        return svg if isinstance(svg, str) else None
    except Exception:
        return None

def try_render_wavedrom_cli(json_path: pathlib.Path, out_svg: pathlib.Path) -> bool:
    if not shutil.which("wavedrom-cli"):
        return False
    try:
        subprocess.run(
            ["wavedrom-cli", str(json_path), "-s", "-o", str(out_svg)],
            check=True
        )
        return out_svg.exists()
    except subprocess.CalledProcessError:
        return False

def rewrite_wavedrom_images(md_text: str, base_dir: pathlib.Path, tmp_img_dir: pathlib.Path) -> str:
    def _sub(m):
        alt, rel = m.group(1), m.group(2)
        jp = (base_dir / rel).resolve()
        if not jp.exists():
            return f"[{alt or 'diagram (wavedrom)'}]({rel})"
        svg_text = try_render_wavedrom_python(jp)
        if svg_text:
            out_svg = tmp_img_dir / (jp.stem + ".svg")
            write_text(out_svg, svg_text)
            return f"![{alt}]({out_svg.as_posix()})"
        out_svg = tmp_img_dir / (jp.stem + ".svg")
        if try_render_wavedrom_cli(jp, out_svg):
            return f"![{alt}]({out_svg.as_posix()})"
        return f"[{alt or 'diagram (wavedrom)'}]({rel})"
    return IMG_JSON_RE.sub(_sub, md_text)

# ---------------------------
# Pandoc runners
# ---------------------------

def build_resource_path(args, input_path: pathlib.Path) -> str:
    paths = [str(pathlib.Path(a).resolve()) for a in args.assets_dir]
    paths.append(str(input_path.resolve().parent))
    seen = set()
    dedup = []
    for p in paths:
        if p not in seen:
            seen.add(p)
            dedup.append(p)
    return ":".join(dedup)

def run_pandoc_docx(md_path: pathlib.Path, out_docx: pathlib.Path, args):
    pandoc = shutil.which("pandoc")
    if not pandoc:
        raise RuntimeError("pandoc not found on PATH")
    cmd = [
        pandoc, str(md_path), "-o", str(out_docx),
        "--standalone",
        "--from", "markdown+yaml_metadata_block+pipe_tables+fenced_code_blocks",
    ]
    if args.reference_doc:
        cmd += ["--reference-doc", args.reference_doc]
    if args.toc:
        cmd += ["--toc", "--toc-depth=3"]
    if args.number_sections:
        cmd += ["--number-sections"]
    if args.quiet:
        cmd += ["--quiet"]
    cmd += ["--resource-path", build_resource_path(args, pathlib.Path(args.input))]
    cmd += ["-V", "graphics=true"]  # help Pandoc with figures/pagebreaks
    if not args.quiet:
        log(f"DOCX command: {' '.join(cmd)}")
    subprocess.run(cmd, check=True)

def run_pandoc_pdf(md_path: pathlib.Path, out_pdf: pathlib.Path, args, tmp_dir: pathlib.Path = None):
    pandoc = shutil.which("pandoc")
    if not pandoc:
        raise RuntimeError("pandoc not found on PATH")
    engine = args.pdf_engine or "xelatex"
    cmd = [
        pandoc, str(md_path), "-o", str(out_pdf),
        "--standalone",
        "--from", "markdown+yaml_metadata_block+pipe_tables+fenced_code_blocks",
        f"--pdf-engine={engine}",
        "--resource-path", build_resource_path(args, pathlib.Path(args.input)),
    ]
    if args.toc:
        cmd += ["--toc", "--toc-depth=3"]
    if args.number_sections:
        cmd += ["--number-sections"]
    if args.quiet:
        cmd += ["--quiet"]

    # --- Font controls: sensible defaults for wide Unicode coverage ---
    default_main = "DejaVu Serif"
    default_mono = "DejaVu Sans Mono"
    mainfont = args.mainfont or default_main
    monofont = args.monofont or default_mono
    cmd += ["-V", f"mainfont={mainfont}", "-V", f"monofont={monofont}"]
    if args.sansfont:
        cmd += ["-V", f"sansfont={args.sansfont}"]
    if args.mathfont:
        cmd += ["-V", f"mathfont={args.mathfont}"]

    # --- Hyperref configuration for clickable links and PDF bookmarks ---
    cmd += ["-V", "colorlinks=true"]
    cmd += ["-V", "linkcolor=blue"]
    cmd += ["-V", "toccolor=blue"]
    cmd += ["-V", "urlcolor=blue"]
    cmd += ["-V", "bookmarks=true"]
    cmd += ["-V", "bookmarksnumbered=true"]

    # Margin control
    if args.narrow_margins:
        cmd += ["-V", "geometry:margin=0.75in"]

    # Section breaks - start each top-level section on a new page
    if args.section_breaks and tmp_dir:
        # Use titlesec package to add \clearpage before each section
        header_tex = tmp_dir / "section_breaks.tex"
        write_text(header_tex, r"""
\usepackage{titlesec}
\newcommand{\sectionbreak}{\clearpage}
""")
        cmd += ["--include-in-header", str(header_tex)]

    if not args.quiet:
        log(f"PDF command: {' '.join(cmd)}")
    subprocess.run(cmd, check=True)

# ---------------------------
# Main
# ---------------------------

def parse_args():
    p = argparse.ArgumentParser(
        description="Convert Markdown (single file or expanded index) to DOCX/PDF via Pandoc."
    )
    p.add_argument("input", help="Input Markdown file (index or chapter).")
    p.add_argument("output", help="Output .docx filename (PDF uses same basename).")
    p.add_argument("--reference-doc", help="Path to a DOCX reference (template).")
    p.add_argument("--pdf", action="store_true", help="Also emit a PDF with same basename.")
    p.add_argument("--toc", action="store_true", help="Include a table of contents.")
    p.add_argument("--number-sections", action="store_true", help="Number sections (1, 1.1, 1.1.1, etc.).")
    p.add_argument("--quiet", action="store_true", help="Reduce Pandoc chatter.")
    p.add_argument("--pagebreak", action="store_true", help="Insert page breaks between concatenated files.")
    p.add_argument("--assets-dir", action="append", default=[],
                help="Add an assets/resource directory (repeatable).")
    p.add_argument("--title-page", nargs="?", const="__AUTO__",
                help="Prepend a title page. If value omitted, auto-generate; otherwise treat as path to a .md file.")
    p.add_argument("--expand-index", action="store_true",
                help="Parse the input index and inline linked chapter .md files in order.")
    p.add_argument("--skip-index-content", action="store_true",
                help="When using --expand-index, don't include the index file content (only chapters).")
    p.add_argument("--debug-md", action="store_true",
                help="Save the merged markdown file for debugging (as output.build.md).")
    p.add_argument("--no-mermaid", action="store_true",
                help="Skip mermaid rendering (leave as code blocks for faster generation).")
    p.add_argument("--narrow-margins", action="store_true",
                help="Use narrow margins (0.75in) for more content per page.")
    p.add_argument("--section-breaks", action="store_true",
                help="Start each top-level section on a new page (PDF only).")
    p.add_argument("--pdf-engine", default=None,
                help="Override PDF engine (default: xelatex).")
    # Font controls (XeLaTeX/LuaLaTeX)
    p.add_argument("--mainfont", default=None, help="Main text font (e.g., 'DejaVu Serif', 'Noto Serif').")
    p.add_argument("--monofont", default=None, help="Monospace font (e.g., 'DejaVu Sans Mono', 'Noto Sans Mono').")
    p.add_argument("--sansfont", default=None, help="Sans-serif font (optional).")
    p.add_argument("--mathfont", default=None, help="Math font (optional).")
    return p.parse_args()

def make_title_page(auto_token: str, primary_input: pathlib.Path) -> str:
    if auto_token != "__AUTO__":
        tp = pathlib.Path(auto_token)
        return read_text(tp)
    title = primary_input.stem.replace("_", " ").replace("-", " ").title()
    today = date.today().isoformat()
    return f"# {title}\n\n**Generated:** {today}\n\n"

def main():
    args = parse_args()
    in_path = pathlib.Path(args.input).resolve()
    out_docx = pathlib.Path(args.output).with_suffix(".docx")
    out_pdf  = out_docx.with_suffix(".pdf")

    with tempfile.TemporaryDirectory() as td:
        tmp_dir = pathlib.Path(td)
        build_md = tmp_dir / "build.md"
        tmp_imgs = tmp_dir / "gen_images"
        tmp_imgs.mkdir(exist_ok=True)

        # Determine source set
        if args.expand_index:
            files = collect_from_index(in_path, skip_index=args.skip_index_content)
            if not files:
                files = [in_path]
        else:
            files = [in_path]

        # Build merged markdown
        chunks = []
        if args.title_page:
            chunks.append(make_title_page(args.title_page, in_path))

        merged = concat_markdown(files, args.pagebreak)
        merged = strip_or_map_emoji(merged)
        merged = rewrite_wavedrom_images(merged, in_path.parent, tmp_imgs)
        if not args.no_mermaid:
            merged = rewrite_mermaid_blocks(merged, tmp_imgs, args.quiet)

        chunks.append(merged)
        final_md = ("\n".join(chunks)).strip() + "\n"
        write_text(build_md, final_md)

        # Debug: save the merged markdown for inspection
        if args.debug_md:
            debug_md_path = pathlib.Path(args.output).with_suffix(".build.md")
            write_text(debug_md_path, final_md)
            log(f"Debug: saved merged markdown to {debug_md_path}")

        # Generate DOCX
        run_pandoc_docx(build_md, out_docx, args)

        # Optional PDF
        if args.pdf:
            try:
                run_pandoc_pdf(build_md, out_pdf, args, tmp_dir)
            except subprocess.CalledProcessError:
                # Fallback: LibreOffice convert from DOCX, if present
                soffice = shutil.which("soffice")
                if not soffice:
                    raise
                subprocess.run([
                    soffice, "--headless", "--convert-to", "pdf",
                    "--outdir", str(out_pdf.parent), str(out_docx)
                ], check=True)

    if not args.quiet:
        log(f"✓ Wrote {out_docx}")
        if args.pdf:
            log(f"✓ Wrote {out_pdf}")

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)
