---
description: Compare all sprint opportunities and generate prioritization matrix
argument-hint: none
allowed-tools: Read, Write, Glob
---

# Compare All Sprints

You are executing the `/compare-sprints` command to rank and prioritize all opportunities.

## Purpose

Compare all executed sprints, rank by opportunity score, identify strategic patterns, and generate prioritization matrix with execution phasing recommendations.

## Steps to Execute

### Step 1: Discover All Reports

Use Glob to find all files: reports/*-report.md
Exclude reports/00-* (comparative/discovery reports)

### Step 2: Extract Key Metrics

For each sprint report, extract:
- Sprint name and number
- Opportunity score (0-100)
- Recommendation tier
- TAM/SAM/SOM estimates
- Timeline to market
- Investment required
- Key differentiators

### Step 3: Create Comparison Matrix

Build table with columns:
- Sprint | Name | Score | Rec | TAM | SAM | SOM | Timeline | Investment | Priority

### Step 4: Rank by Composite Score

Sort opportunities by opportunity score (highest first).
Identify strategic themes and synergies.
Group complementary opportunities.

### Step 5: Generate 4-Tier Prioritization

Tier 1 (Execute Immediately): Scores 80-100, high strategic fit
Tier 2 (Execute Soon): Scores 65-79, good opportunities
Tier 3 (Consider): Scores 50-64, conditional execution
Deprioritize: Scores <50, risks outweigh benefits

### Step 6: Create Strategic Roadmap

Phase 1 (0-6 months): Tier 1 sprints
Phase 2 (6-12 months): Tier 2 sprints
Phase 3 (12-24 months): Tier 3 sprints (if conditions met)

### Step 7: Write Comparison Report

Create reports/00-cross-sprint-analysis.md with:
- Comparison matrix
- Prioritization tiers
- Strategic roadmap
- Aggregate metrics (total TAM, investment)
- Recommendations and rationale

### Step 8: Output Summary

Display top 3 priorities and key insights.

## Success Criteria

- All sprint reports analyzed
- Comparison matrix complete
- Prioritization tiers assigned
- Strategic roadmap created
- Comparison report written

## Error Handling

If fewer than 2 reports, cannot compare.

## Expected Output

User receives comparison report with clear prioritization and strategic guidance.
