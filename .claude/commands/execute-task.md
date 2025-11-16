---
description: Execute a single task within a sprint using appropriate research skill
argument-hint: [sprint-number] [task-number]
allowed-tools: Task, Read, Write, Grep, Glob, TodoWrite, WebSearch, WebFetch
---

# Execute Single Task

You are executing the `/execute-task` command to run one task within a sprint.

## Purpose

Execute a single research task by invoking the appropriate specialized skill (technical-researcher, market-analyst, solution-architect, compliance-analyst, roadmap-planner, or report-synthesizer) with full context.

## Steps to Execute

### Step 1: Validate Arguments

Check $1 (sprint-number) is 2-digit format 01-99
Check $2 (task-number) is 01-06
Verify prerequisites:
- Sprint $1 exists in config/sprint-config.yml
- Task file exists: sprints/$1-*/0$2-*.md
- Context files populated

### Step 2: Load Configuration and Context

Read config/project-config.yml for execution parameters
Read config/sprint-config.yml for sprint details
Read context files (client-info.md, company-profile.md)
Read task definition file: sprints/$1-*/0$2-*.md

### Step 3: Determine Appropriate Skill

Map task number to skill:
- Task 01 → technical-researcher (or research-synthesizer with technical focus)
- Task 02 → market-analyst (or research-synthesizer with market focus)
- Task 03 → solution-architect (or research-synthesizer with architecture focus)
- Task 04 → compliance-analyst (or research-synthesizer with compliance focus)
- Task 05 → roadmap-planner (or research-synthesizer with roadmap focus)
- Task 06 → report-synthesizer

### Step 4: Invoke Skill via Task Tool

Use Task tool to invoke appropriate skill with context:
- Sprint number: $1
- Task number: $2
- Configuration paths
- Context file contents
- Output directory: temp/$1-*/0$2-*/

Skill will autonomously:
- Research according to task questions
- Create 5-7 research files
- Generate synthesis document
- Cite all claims with authoritative sources

### Step 5: Monitor Execution

Track skill progress
Update progress tracking tool if monitoring task list
Handle any errors gracefully

### Step 6: Validate Task Output

Verify:
- temp/$1-*/0$2-*/ directory exists
- Minimum 5 research files created
- synthesis.md file exists
- Files are substantive (>500 words each)
- Citations present

### Step 7: Output Task Summary

Display:
- Files created (count and names)
- Word count total
- Key findings summary
- Citations count
- Success confirmation

## Success Criteria

- Task directory created with 5+ research files
- Synthesis document exists
- All research cited with sources
- Output quality meets standards

## Error Handling

If invalid sprint/task numbers, provide usage example.
If prerequisites missing, guide user to run /init-project or /create-sprint.
If skill execution fails, provide diagnostic information.

## Expected Output

User receives task completion summary with file counts, findings, and next steps.
