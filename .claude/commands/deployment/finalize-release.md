# Finalize Release

## Objective
Create git release/tag for completed sprint, archive findings, and prepare for next sprint.

## Usage
```
/finalize-release 01
```

## Release Process

### 1. Verify Sprint Complete
- Confirm all tasks (01-06) are complete
- Verify final report exists
- Check quality validation passed
- Ensure all findings committed to git

### 2. Create Git Tag
```bash
git tag -a sprint-01-complete -m "Sprint 01: [Sprint Name] - Complete

Final Score: [score]/100
Recommendation: [Go/No-Go]
Research Files: [count]
Report Date: [date]"
```

### 3. Update CHANGELOG
Add sprint completion to CHANGELOG.md:
```markdown
## Sprint 01 - [Sprint Name] - [Date]

### Completed
- Technical & Regulatory Landscape Research
- Market & Competitive Assessment
- Solution Architecture Design
- Certification & Testing Strategy
- Implementation Roadmap
- Final Report Synthesis

### Deliverables
- Research files: [count] files in temp/sprint-01/
- Final report: reports/sprint-01-final-report.md
- Opportunity score: [score]/100
- Recommendation: [Go/No-Go with brief rationale]

### Key Findings
- [Key finding 1]
- [Key finding 2]
- [Key finding 3]
```

### 4. Archive Research Files (Optional)
If desired, create compressed archive:
```bash
tar -czf archives/sprint-01-research.tar.gz temp/sprint-01/
```

### 5. Push to Remote
```bash
git add .
git commit -m "Sprint 01: Finalize release"
git push origin main
git push --tags
```

### 6. Prepare for Next Sprint
- Clear temp/sprint-01/ if desired (or keep for reference)
- Update sprint-config.yml for next sprint
- Review and update context files if needed

## Output
- Git tag created: `sprint-01-complete`
- CHANGELOG updated
- Changes committed and pushed
- Optional: Research archive created
- Repository ready for next sprint
