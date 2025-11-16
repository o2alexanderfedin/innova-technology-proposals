# Execute Single Task

## Objective
Execute a single task within a sprint.

## Usage
```
/execute-task 01 03
```
(Sprint 01, Task 03)

## Steps to Execute

### 1. Validate Task Exists
- Check `config/sprint-config.yml` for sprint and task definitions
- Verify task directory exists in `temp/sprint-XX/`

### 2. Determine Specialist Skill
- Task 01: `technical-researcher`
- Task 02: `market-analyst`
- Task 03: `solution-architect`
- Task 04: `compliance-analyst`
- Task 05: `roadmap-planner`
- Task 06: `report-synthesizer`

### 3. Load Context
- Read project configuration
- Read context files
- Read results from previous tasks (if dependencies)

### 4. Invoke Specialist Skill
- Execute skill with appropriate context
- Skill creates research files in `temp/sprint-XX/0X-taskname/`
- Monitor progress

### 5. Validate Output
- Verify minimum file count met
- Check citation coverage
- Validate file format and structure

## Output
- Research files created in task directory
- Quality metrics reported
- Task marked complete
