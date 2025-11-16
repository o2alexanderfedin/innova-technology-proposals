---
description: Synthesize final strategic report for a sprint with scoring
argument-hint: [sprint-number]
allowed-tools: Task, Read, Write
---

# Synthesize Final Report

You are executing the `/synthesize-report` command to create the final strategic report for sprint $1.

## Purpose

Synthesize all research findings from Tasks 01-05 into a comprehensive 10-page strategic report (5,000-7,500 words) with opportunity scoring and clear go/no-go recommendation.

## Steps to Execute

### Step 1: Validate Sprint Number

Check $1 is valid sprint number 01-99.
Verify sprint executed (temp/$1-*/ has research files).

### Step 2: Verify Prerequisites

Check minimum file count: temp/$1-*/ should have 25+ research files.
Verify synthesis documents exist for Tasks 01-05.
Confirm config/scoring-rubric.yml exists.

### Step 3: Invoke Report Generator Skill

Use Task tool to invoke report-generator skill with context:
- Sprint number: $1
- Research directory: temp/$1-*/
- Scoring rubric: config/scoring-rubric.yml
- Output path: reports/$1-*-report.md

Report generator skill will:
- Read all research files from Tasks 01-05
- Apply scoring rubric (5 dimensions, weighted)
- Generate comprehensive report with required sections
- Calculate opportunity score (0-100)
- Provide go/no-go recommendation

### Step 4: Validate Report Output

Check reports/$1-*-report.md exists.
Verify word count: 5,000-7,500 words.
Confirm all required sections present.
Validate opportunity score included.

### Step 5: Output Success Summary

Display report statistics and key findings.

## Success Criteria

- Report created: reports/$1-*-report.md
- Word count: 5,000-7,500 words
- All sections present
- Opportunity score: 0-100
- Clear recommendation

## Error Handling

If prerequisites missing, guide user to execute sprint first.

## Expected Output

User receives confirmation of report creation with score and recommendation.
