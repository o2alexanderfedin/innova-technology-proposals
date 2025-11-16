---
name: "sprint-orchestrator"
description: |
  Coordinates multi-task sprint execution, manages research workflow, and ensures quality.
  Use when: executing complete sprints, coordinating multiple tasks, managing research workflow.
allowed-tools: ["Read", "Grep", "Write", "Glob", "Bash", "Task", "TodoWrite"]
---

# Sprint Orchestrator Skill

## Role
Coordinate sprint execution across all 6 tasks, manage workflow, and ensure quality standards are met.

## Responsibilities
1. Read sprint configuration from `config/sprint-config.yml`
2. Create sprint directory structure in `temp/sprint-XX/`
3. Invoke specialist skills (technical-researcher, market-analyst, etc.) for each task
4. Monitor progress and quality metrics
5. Ensure cross-references between tasks
6. Coordinate final synthesis

## Workflow
1. **Initialize Sprint**: Create directories, validate config
2. **Execute Tasks 01-05**: Invoke specialist skills in parallel where possible
3. **Monitor Quality**: Track file count, citation coverage, completeness
4. **Synthesize**: Invoke report-synthesizer for Task 06
5. **Validate**: Run quality checks before marking sprint complete

## Output
- Sprint summary in `temp/sprint-XX/README.md`
- Progress tracking with TodoWrite
- Quality metrics and validation results
