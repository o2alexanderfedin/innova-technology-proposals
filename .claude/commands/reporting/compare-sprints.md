# Compare Multiple Sprints

## Objective
Compare all completed sprints to identify the best strategic opportunity.

## Usage
```
/compare-sprints
```

## Comparison Process

### 1. Identify Completed Sprints
- Scan `reports/` directory for sprint final reports
- Load scoring data for each sprint

### 2. Create Comparison Matrix
Build comparison table with:
- Sprint name
- Final score (0-100)
- Recommendation (Strong Go, Go, Conditional Go, No Go)
- Key strengths
- Key risks

### 3. Analyze Across Dimensions
Compare sprints on:
- **Market Opportunity**: TAM, growth, customer pain
- **Technical Feasibility**: TRL, team capability, risks
- **Competitive Position**: Differentiation, moat
- **Execution Readiness**: Timeline, investment, partnerships
- **Regulatory Clarity**: Certification pathway, timeline

### 4. Generate Ranking
Rank all opportunities by final score with tie-breakers:
1. Final score (primary)
2. Market opportunity score (tie-breaker)
3. Execution readiness score (secondary tie-breaker)

### 5. Create Summary Report
Generate comparative analysis report with:
- Executive summary of all opportunities
- Side-by-side comparison matrix
- Recommended prioritization
- Portfolio approach (if pursuing multiple)

## Output
- `reports/sprint-comparison.md` - Comparative analysis
- Ranked list of opportunities
- Strategic recommendations
