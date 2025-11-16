# Initialize New Strategic Research Project

## Objective
Set up a new strategic research project from this template repository.

## Steps to Execute

### 1. Copy Configuration Files
```bash
cp config/project-config.yml config/project-config.yml
# (Already in place, user should edit)
```

### 2. Create Workspace Directories
```bash
mkdir -p context sprints temp reports
```

### 3. Copy Environment Template
```bash
cp .env.example .env
# User must edit .env to add ANTHROPIC_API_KEY
```

### 4. Create Context Files
Create the following files in `context/` directory:
- `company-profile.md` - Your company's capabilities, goals, constraints
- `client-info.md` - Client background, requirements, preferences (or use "Internal" for internal projects)
- `industry-background.md` - Industry-specific knowledge and context

### 5. Customize Project Configuration
Edit `config/project-config.yml`:
- Replace {{PROJECT_NAME}}, {{COMPANY_NAME}}, {{CLIENT_NAME}}, {{INDUSTRY}}
- Adjust research.max_parallel_tasks based on system capabilities
- Configure output.export_formats (markdown, pdf, docx)

### 6. Define Sprints
Edit `config/sprint-config.yml`:
- Define research sprints (opportunities to investigate)
- Customize sprint names and descriptions
- Adjust estimated_duration as needed

### 7. Customize Quality Standards (Optional)
Edit `config/quality-standards.yml` and `config/scoring-rubric.yml` if needed

### 8. Initialize Git Repository
```bash
git init
git add .
git commit -m "Initial commit: Strategic research project setup"
```

## Validation
Run validation to ensure setup is correct:
```bash
./scripts/validate-structure.sh
```

## Next Steps
After initialization, create your first sprint:
```
/create-sprint "Your First Opportunity Name"
```

## Output
- Workspace directories created
- Configuration files customized
- Environment variables configured
- Git repository initialized
- Project ready for sprint execution
