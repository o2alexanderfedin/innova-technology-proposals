# Validate Quality Standards

## Objective
Run quality assurance checks on sprint research and reports.

## Usage
```
/validate-quality 01
```

## Quality Checks

### 1. Citation Coverage
- Parse all research files for citations
- Calculate citation coverage percentage
- Compare against threshold in `config/quality-standards.yml`
- Report files with insufficient citations

### 2. Cross-Reference Validation
- Extract all internal markdown links
- Verify all links resolve to existing files/sections
- Report broken links

### 3. Terminology Consistency
- Check usage against `config/glossary.yml`
- Identify inconsistent term usage
- Suggest corrections

### 4. File Count Validation
- Count research files per task
- Verify minimum file count met (from config)
- Report tasks below threshold

### 5. Document Structure
- Verify each file has required sections:
  - Executive Summary
  - Key Findings
  - Supporting Evidence
  - References
- Report structural issues

### 6. File Size Check
- Verify files are within word count range (500-5000 words)
- Report files that are too short or too long

## Output
- Quality validation report
- Pass/Fail status for each check
- List of issues with file/line references
- Recommendations for remediation
