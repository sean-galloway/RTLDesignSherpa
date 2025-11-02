# Usage Guide for `md_to_docx.py`

This script converts a main Markdown file (and all linked `.md` files) into a styled Word `.docx` or PDF.

---

## 📄 Basic Usage

```bash
python md_to_docx.py input.md
```

This creates `output.docx` using default Pandoc styling.

---

## 🧩 Common Options

### `-t` or `--template`

Specify a Word template (`.dotx` or `.docx`) for styling:

```bash
python md_to_docx.py input.md -t my_template.dotx
```

If you use `.dotx`, it will be auto-converted to `.docx`.

---

### `-o` or `--output`

Set output file name:

```bash
python md_to_docx.py input.md -o final_output.docx
```

---

### `--toc`

Include a **Table of Contents**:

```bash
python md_to_docx.py input.md --toc
```

---

### `--title-page`

Add a title page using default metadata (or YAML frontmatter if present):

```bash
python md_to_docx.py input.md --title-page
```

---

### `--pdf`

Also create a `.pdf` alongside `.docx`:

```bash
python md_to_docx.py input.md --pdf
```

Requires Pandoc **and** LaTeX installed.

---

### `--debug-md`

Write merged markdown to `debug.md` for inspection:

```bash
python md_to_docx.py input.md --debug-md
```

---

### `--verbose`

Enable detailed logging output:

```bash
python md_to_docx.py input.md --verbose
```

---

## 🧠 Example Combo

```bash
python md_to_docx.py input.md -t style.dotx -o report.docx --toc --title-page --pdf --verbose
```

---

## 📌 Notes

- Use relative Markdown links like `[Section](section1.md)` in your `input.md`
- Image paths must be correct relative to their source files
- YAML metadata (title, author, date) is supported in `input.md`