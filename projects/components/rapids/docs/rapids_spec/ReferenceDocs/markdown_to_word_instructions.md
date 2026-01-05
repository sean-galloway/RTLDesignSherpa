<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Markdown to Word Converter - Usage Instructions

## Overview

This Python script converts markdown files into Microsoft Word documents (.docx), preserving formatting, structure, and images. It supports both individual file conversion and structured document creation using an index file.

## Prerequisites

### Required Python Packages

Install the required dependencies using pip:

```bash
pip install python-docx markdown beautifulsoup4 requests
```

### Package Details

- **python-docx**: Creates and manipulates Word documents
- **markdown**: Converts markdown to HTML
- **beautifulsoup4**: Parses HTML content
- **requests**: Downloads images from URLs

## Basic Usage

### Command Line Interface

The script uses command line arguments for operation:

```bash
python markdown_to_word.py --dir <input_directory> --out <output_file.docx>
```

### Arguments

| Argument | Required | Description | Example |
|----------|----------|-------------|---------|
| `--dir` | Yes | Path to directory containing markdown files | `./docs` |
| `--out` | Yes | Output Word document filename | `manual.docx` |

## Directory Structure

### Required Files

Your markdown directory must contain:

1. **index.md** - Defines the document structure and chapter organization
2. **Markdown files** - Content files referenced in index.md
3. **Images** (optional) - Referenced images in markdown files

### Example Directory Layout

```
docs/
+-- index.md                 # Structure definition
+-- introduction.md          # Chapter content
+-- getting-started.md       # Chapter content
+-- advanced-topics.md       # Chapter content
+-- best-practices.md        # Chapter content
+-- images/                  # Image assets
    +-- diagram1.png
    +-- screenshot1.jpg
    +-- logo.svg
```

## Creating index.md

The `index.md` file defines your document structure using markdown headings and links.

### Basic Format

```markdown
# Document Title

## Chapter 1: Introduction
- [Getting Started](getting-started.md)
- [Basic Concepts](basic-concepts.md)

## Chapter 2: Advanced Topics
- [Advanced Features](advanced-topics.md)
- [Best Practices](best-practices.md)

## Appendix
- [Troubleshooting](troubleshooting.md)
- [FAQ](faq.md)
```

### Structure Rules

1. **Headings** (`#`, `##`, `###`) define chapter levels
2. **Links** in lists point to markdown files: `[Title](filename.md)`
3. **File paths** are relative to the directory containing index.md
4. **Multiple files** can be included under each chapter

### Advanced Structure Example

```markdown
# Technical Documentation

## Part 1: Fundamentals

### Chapter 1: Getting Started
- [Installation](install.md)
- [Configuration](config.md)

### Chapter 2: Basic Usage
- [First Steps](first-steps.md)
- [Common Tasks](common-tasks.md)

## Part 2: Advanced Topics

### Chapter 3: Architecture
- [System Design](architecture.md)
- [Performance](performance.md)

### Chapter 4: Integration
- [API Reference](api.md)
- [Examples](examples.md)
```

## Supported Markdown Features

### Text Formatting

```markdown
**Bold text**
*Italic text*
`Inline code`
[Links](http://example.com)
```

### Headings

```markdown
# Heading 1
## Heading 2
### Heading 3
#### Heading 4
##### Heading 5
###### Heading 6
```

### Lists

```markdown
- Bullet point 1
- Bullet point 2
  - Nested item
  - Another nested item

1. Numbered item 1
2. Numbered item 2
3. Numbered item 3
```

### Code Blocks

```markdown
```python
def hello_world():
    print("Hello, World!")
```
```

### Blockquotes

```markdown
> This is a blockquote
> with multiple lines
```

### Images

```markdown
![Alt text](images/diagram.png)
![Remote image](https://example.com/image.jpg)
```

## Image Handling

### Local Images

- Place images in subdirectories (e.g., `images/`)
- Use relative paths in markdown: `![Alt text](images/photo.jpg)`
- Supported formats: PNG, JPG, JPEG, GIF, BMP, SVG

### Remote Images

- URLs are automatically downloaded during conversion
- Images are temporarily cached and cleaned up
- Failed downloads show placeholder text

### Image Sizing

- Images are automatically resized to fit page width (max 6 inches)
- Alt text becomes image captions in the Word document
- Images maintain aspect ratio

## Usage Examples

### Simple Document

Create a basic document from a few markdown files:

**Directory structure:**
```
my-docs/
+-- index.md
+-- intro.md
+-- conclusion.md
```

**index.md content:**
```markdown
# My Document

## Introduction
- [Introduction](intro.md)

## Conclusion  
- [Conclusion](conclusion.md)
```

**Command:**
```bash
python markdown_to_word.py --dir my-docs --out my-document.docx
```

### Complex Technical Manual

Create a multi-chapter technical manual:

**Directory structure:**
```
technical-manual/
+-- index.md
+-- chapters/
|   +-- 01-introduction.md
|   +-- 02-installation.md
|   +-- 03-configuration.md
|   +-- 04-usage.md
|   +-- 05-troubleshooting.md
+-- assets/
    +-- screenshots/
    +-- diagrams/
```

**index.md content:**
```markdown
# Technical Manual v2.0

## Getting Started
- [Introduction](chapters/01-introduction.md)
- [Installation Guide](chapters/02-installation.md)

## Configuration
- [Configuration](chapters/03-configuration.md)

## User Guide
- [Usage Instructions](chapters/04-usage.md)

## Support
- [Troubleshooting](chapters/05-troubleshooting.md)
```

**Command:**
```bash
python markdown_to_word.py --dir technical-manual --out technical-manual-v2.docx
```

### API Documentation

Convert API documentation with code examples:

**Directory structure:**
```
api-docs/
+-- index.md
+-- overview.md
+-- authentication.md
+-- endpoints/
|   +-- users.md
|   +-- projects.md
|   +-- reports.md
+-- examples/
    +-- curl-examples.md
    +-- python-examples.md
```

**Command:**
```bash
python markdown_to_word.py --dir api-docs --out api-documentation.docx
```

## Output Features

### Word Document Structure

The generated Word document includes:

- **Title page** with document name and file count
- **Proper heading hierarchy** based on markdown structure
- **Table of contents** (can be generated in Word after conversion)
- **Formatted text** with bold, italic, and code formatting
- **Bulleted and numbered lists**
- **Images** with captions
- **Code blocks** in monospace font
- **Page breaks** between major sections

### Styling

The script applies standard Word styles:

- Heading 1-6 styles for markdown headings
- List Bullet and List Number styles for lists
- Quote style for blockquotes
- Courier New font for code blocks
- Automatic hyperlink formatting

## Troubleshooting

### Common Issues

**1. "No markdown files found"**
- Ensure `index.md` exists in the specified directory
- Check that linked files in index.md exist
- Verify file paths are relative to the index.md location

**2. "File not found" errors**
- Check that all files referenced in index.md exist
- Ensure file paths use forward slashes (/)
- Verify file extensions are .md

**3. Images not appearing**
- Check image file paths are correct
- Ensure images exist in specified locations
- For remote images, check internet connectivity

**4. Formatting issues**
- Ensure markdown syntax is correct
- Check for proper heading hierarchy
- Verify list formatting (spaces and indentation)

### Debug Tips

1. **Test with simple structure first**
2. **Check file paths carefully**
3. **Verify markdown syntax**
4. **Run script from correct directory**
5. **Check console output for error messages**

## Advanced Configuration

### Customizing Styles

To modify the document appearance, edit the `setup_styles()` method in the script:

```python
def setup_styles(self):
    styles = self.doc.styles
    
    # Customize heading styles
    heading1 = styles['Heading 1']
    heading1.font.size = Pt(16)
    heading1.font.color.rgb = RGBColor(0, 0, 128)
```

### Adding Custom Processing

Extend the `add_element_to_doc()` method to handle custom markdown extensions or modify formatting behavior.

### Batch Processing

For multiple document sets, create a wrapper script:

```python
import os
from markdown_to_word import MarkdownToWordConverter

docs = [
    ('user-manual', 'user-manual.docx'),
    ('admin-guide', 'admin-guide.docx'),
    ('api-docs', 'api-reference.docx')
]

for doc_dir, output_file in docs:
    converter = MarkdownToWordConverter()
    converter.convert_directory_with_index(doc_dir, output_file)
    print(f"Completed: {output_file}")
```

## Best Practices

### File Organization

1. **Use descriptive filenames** with consistent naming conventions
2. **Group related content** in subdirectories
3. **Keep image assets** in dedicated folders
4. **Use meaningful alt text** for images
5. **Test markdown rendering** before conversion

### Content Structure

1. **Plan document hierarchy** before writing
2. **Use consistent heading levels**
3. **Keep file sizes reasonable** (split large chapters)
4. **Include descriptive link text** in index.md
5. **Test index.md structure** with a simple example first

### Quality Control

1. **Preview markdown** in a markdown editor
2. **Check all links and images** work
3. **Review generated Word document** for formatting
4. **Test with different content types** (tables, code, images)
5. **Validate file paths** are portable across systems

This script provides a powerful way to create professional Word documents from markdown content while maintaining structure and formatting.