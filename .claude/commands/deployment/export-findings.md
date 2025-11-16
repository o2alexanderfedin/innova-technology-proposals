# Export Findings

## Objective
Export final reports to PDF, DOCX, or other formats for stakeholder distribution.

## Usage
```
/export-findings 01 pdf
```

## Export Process

### 1. Verify Pandoc Installation
Check if pandoc is installed (required for PDF/DOCX export):
```bash
pandoc --version
```

If not installed:
- macOS: `brew install pandoc`
- Linux: `apt-get install pandoc`
- Windows: Download from pandoc.org

### 2. Select Export Format
Supported formats:
- **markdown**: Native format (always available)
- **pdf**: Requires pandoc + LaTeX
- **docx**: Requires pandoc
- **html**: Requires pandoc

### 3. Prepare Document
- Ensure final report exists
- Verify all images and links resolve
- Check formatting for target format

### 4. Execute Export
```bash
pandoc reports/sprint-01-final-report.md \
  -o reports/sprint-01-final-report.pdf \
  --pdf-engine=xelatex \
  --toc \
  --number-sections \
  --metadata title="Strategic Opportunity Analysis"
```

### 5. Validate Output
- Open exported file
- Verify formatting is correct
- Check images rendered properly
- Ensure links work (where applicable)

## Export Options

### PDF Export
- Table of contents
- Numbered sections
- Professional styling
- Embedded images

### DOCX Export
- Styled headings
- Consistent formatting
- Editable for stakeholder comments
- Track changes enabled

### HTML Export
- Interactive navigation
- Responsive design
- Embedded multimedia

## Output
- Exported files in `reports/` directory
- Multiple formats as specified
- Ready for stakeholder distribution
