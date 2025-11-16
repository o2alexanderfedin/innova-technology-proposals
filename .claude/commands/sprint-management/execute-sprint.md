# Execute Complete Sprint

## Objective
Execute all 6 tasks in a sprint from start to finish.

## Usage
```
/execute-sprint 01
```

## Execution Flow

### 1. Read Sprint Configuration
- Load sprint definition from `config/sprint-config.yml`
- Read project configuration from `config/project-config.yml`
- Load context files from `context/`

### 2. Invoke Sprint Orchestrator Skill
- Use `sprint-orchestrator` skill to coordinate execution
- The orchestrator will invoke specialist skills for each task:
  - Task 01: `technical-researcher`
  - Task 02: `market-analyst`
  - Task 03: `solution-architect`
  - Task 04: `compliance-analyst`
  - Task 05: `roadmap-planner`
  - Task 06: `report-synthesizer`

### 3. Parallel Execution (Tasks 01-05)
- Tasks 01-05 can execute in parallel where configured
- Each specialist skill creates research files in `temp/sprint-XX/`
- Monitor progress with TodoWrite

### 4. Sequential Synthesis (Task 06)
- Task 06 depends on completion of tasks 01-05
- `report-synthesizer` creates final report
- Applies scoring rubric
- Generates go/no-go recommendation

### 5. Quality Validation
- Verify citation coverage meets threshold
- Check cross-references resolve
- Validate terminology consistency
- Ensure minimum file count met

## Output
- Research files in `temp/sprint-XX/`
- Final report in `reports/sprint-XX-final-report.md`
- Executive summary in `reports/sprint-XX-executive-summary.md`
- Scoring breakdown and recommendation
- Sprint marked complete in tracking
