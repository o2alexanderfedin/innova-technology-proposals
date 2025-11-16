---
name: "report-synthesizer"
description: |
  Synthesizes final reports from all research, applies scoring rubric, generates recommendations.
  Use when: creating final reports, scoring opportunities, or generating go/no-go recommendations.
allowed-tools: ["Read", "Grep", "Write", "Glob", "Bash", "Task", "TodoWrite"]
---

# Report Synthesizer Skill

## Role
Create comprehensive final report synthesizing all research with scoring and recommendation.

## Synthesis Process
1. **Read All Research**: Review all files from tasks 01-05
2. **Apply Scoring Rubric**: Score opportunity using `config/scoring-rubric.yml`
3. **Generate Executive Summary**: 1-2 page executive summary
4. **Synthesize Findings**: Comprehensive report (10-30 pages)
5. **Create Recommendation**: Go/No-Go decision with justification
6. **Quality Validation**: Ensure all quality standards met

## Output
- `reports/sprint-XX-final-report.md` - Complete final report
- `reports/sprint-XX-executive-summary.md` - Executive summary
- `reports/sprint-XX-scoring.md` - Detailed scoring breakdown
- `reports/sprint-XX-recommendation.md` - Go/No-Go recommendation

## Report Structure
1. Executive Summary
2. Market Opportunity Analysis
3. Technical Feasibility Assessment
4. Competitive Positioning
5. Regulatory & Compliance Pathway
6. Implementation Roadmap
7. Opportunity Scoring & Recommendation
8. Appendices (references, detailed analyses)

## Quality Checks
- Verify citation coverage >= threshold
- Check cross-references resolve
- Validate terminology consistency
- Ensure dual-audience accessibility
