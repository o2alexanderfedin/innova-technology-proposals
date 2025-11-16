# Synthesize Final Report

## Objective
Create comprehensive final report synthesizing all research from a sprint.

## Usage
```
/synthesize-report 01
```

## Steps to Execute

### 1. Verify Prerequisites
- Confirm tasks 01-05 are complete
- Verify research files exist for all tasks
- Load quality standards and scoring rubric

### 2. Invoke Report Synthesizer
- Use `report-synthesizer` skill
- Read all research files from `temp/sprint-01/`
- Apply synthesis methodology

### 3. Generate Report Components
- Executive Summary (1-2 pages)
- Market Opportunity Analysis
- Technical Feasibility Assessment
- Competitive Positioning
- Regulatory & Compliance Pathway
- Implementation Roadmap
- Full reference bibliography

### 4. Apply Scoring Rubric
- Score opportunity using `config/scoring-rubric.yml`
- Calculate category scores and final score (0-100)
- Generate detailed scoring breakdown

### 5. Create Recommendation
- Generate go/no-go recommendation based on score
- Provide justification citing key findings
- Identify risks and mitigation strategies

## Output
- `reports/sprint-XX-final-report.md` - Complete report
- `reports/sprint-XX-executive-summary.md` - Executive summary
- `reports/sprint-XX-scoring.md` - Scoring breakdown
- `reports/sprint-XX-recommendation.md` - Go/no-go decision
