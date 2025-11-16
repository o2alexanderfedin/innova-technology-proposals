# Execute All Sprints

## Objective
Execute all defined sprints in sequence or parallel.

## Usage
```
/execute-all
```

## Execution Strategy

### 1. Load Sprint Configuration
- Read `config/sprint-config.yml`
- Identify all defined sprints
- Sort by priority (high, medium, low)

### 2. Determine Execution Mode
Choose based on configuration:

**Sequential Mode** (default):
- Execute sprints one at a time in priority order
- Wait for each sprint to complete before starting next
- Safer approach, allows learning between sprints

**Parallel Mode** (if enabled):
- Execute multiple sprints concurrently
- Respect `research.max_parallel_tasks` limit
- Faster completion but higher resource usage

### 3. Execute Each Sprint
For each sprint:
- Create sprint directory if not exists
- Execute all 6 tasks
- Generate final report
- Apply scoring rubric
- Create recommendation

### 4. Progress Tracking
- Use TodoWrite to track sprint progress
- Report completion percentage
- Estimate time remaining

### 5. Generate Comparison Report
After all sprints complete:
- Compare all opportunities
- Rank by score
- Generate portfolio recommendations

## Output
- All sprint research files in `temp/`
- All final reports in `reports/`
- Comparison report: `reports/all-sprints-comparison.md`
- Recommended prioritization
- Total execution time and statistics
