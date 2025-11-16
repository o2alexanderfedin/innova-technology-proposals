# Score Opportunity

## Objective
Apply scoring rubric to evaluate strategic opportunity.

## Usage
```
/score-opportunity 01
```

## Scoring Process

### 1. Load Scoring Rubric
- Read `config/scoring-rubric.yml`
- Understand categories, weights, and criteria

### 2. Extract Findings
- Review all research files from sprint
- Extract relevant data for each scoring criterion

### 3. Score Each Criterion (0-100)
Evaluate each criterion based on research:
- **90-100**: Exceptional - Market-leading position, minimal risk
- **70-89**: Strong - Clear advantage, manageable risks
- **50-69**: Moderate - Viable but requires significant effort
- **30-49**: Weak - Major challenges, questionable viability
- **0-29**: Poor - Fundamental issues, not recommended

### 4. Calculate Category Scores
For each category:
```
Category Score = Σ (Criterion Weight × Criterion Score)
```

### 5. Calculate Final Score
```
Final Score = Σ (Category Weight × Category Score)
```

### 6. Determine Recommendation
Based on thresholds in rubric:
- **≥80**: Strong Go - Highly recommended
- **65-79**: Go - Recommended with confidence
- **50-64**: Conditional Go - Proceed with caution
- **<50**: No Go - Not recommended

## Output
- Detailed scoring breakdown by category and criterion
- Final score (0-100)
- Recommendation with justification
- Key risk factors and mitigation needs
