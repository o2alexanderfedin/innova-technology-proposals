# Create New Sprint

## Objective
Create a new sprint directory structure for investigating a strategic opportunity.

## Usage
```
/create-sprint "Sprint Name"
```

## Steps to Execute

### 1. Get Next Sprint Number
- Read `config/sprint-config.yml`
- Determine next available sprint ID (01, 02, 03, etc.)

### 2. Add Sprint Configuration
- Add sprint definition to `config/sprint-config.yml`
- Include all 6 tasks (01-technical, 02-market, 03-architecture, 04-certification, 05-roadmap, 06-synthesis)

### 3. Create Sprint Directory Structure
```bash
mkdir -p sprints/sprint-XX
mkdir -p temp/sprint-XX/{01-technical,02-market,03-architecture,04-certification,05-roadmap,06-synthesis}
```

### 4. Create Sprint README
Generate `sprints/sprint-XX/README.md` with:
- Sprint overview and objectives
- Task breakdown with descriptions
- Success criteria
- Timeline estimates

### 5. Instantiate Task Files
Create 6 task markdown files in `sprints/sprint-XX/`:
- `01-technical-requirements-research.md`
- `02-market-competitive-analysis.md`
- `03-solution-architecture-design.md`
- `04-certification-pathway-analysis.md`
- `05-implementation-roadmap.md`
- `06-final-report-synthesis.md`

## Output
- Sprint directory created
- Task files generated from templates
- Configuration updated
- Sprint ready for execution
