#!/usr/bin/env bash
# Setup script for strategic research automation project
# Run this after cloning the template repository

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Functions
print_success() {
  echo -e "${GREEN}✓${NC} $1"
}

print_error() {
  echo -e "${RED}✗${NC} $1"
}

print_warning() {
  echo -e "${YELLOW}⚠${NC} $1"
}

print_header() {
  echo ""
  echo "========================================="
  echo "$1"
  echo "========================================="
  echo ""
}

check_command() {
  if command -v "$1" &> /dev/null; then
    print_success "$1 is installed"
    return 0
  else
    print_warning "$1 is not installed"
    return 1
  fi
}

# Main setup process
main() {
  print_header "Strategic Research Automation - Project Setup"

  # Check dependencies
  print_header "Checking Dependencies"

  MISSING_DEPS=0

  if ! check_command "git"; then
    print_error "git is required but not installed"
    MISSING_DEPS=1
  fi

  # Optional but recommended
  if ! check_command "pandoc"; then
    print_warning "pandoc is recommended for PDF/DOCX export"
    echo "Install with: brew install pandoc (macOS) or apt-get install pandoc (Linux)"
  fi

  if ! check_command "yamllint"; then
    print_warning "yamllint is recommended for config validation"
    echo "Install with: pip install yamllint or brew install yamllint"
  fi

  if [ $MISSING_DEPS -eq 1 ]; then
    print_error "Please install missing dependencies and re-run setup"
    exit 1
  fi

  # Create workspace directories
  print_header "Creating Workspace Directories"

  mkdir -p context
  print_success "Created context/"

  mkdir -p sprints
  print_success "Created sprints/"

  mkdir -p temp
  print_success "Created temp/"

  mkdir -p reports
  print_success "Created reports/"

  # Copy environment template
  print_header "Setting Up Environment"

  if [ ! -f .env ]; then
    cp .env.example .env
    print_success "Created .env from template"
    print_warning "IMPORTANT: Edit .env and add your ANTHROPIC_API_KEY"
  else
    print_warning ".env already exists, skipping"
  fi

  # Initialize git if not already initialized
  print_header "Git Repository"

  if [ ! -d .git ]; then
    git init
    print_success "Initialized git repository"
  else
    print_success "Git repository already initialized"
  fi

  # Create context file templates if they don't exist
  print_header "Creating Context File Templates"

  if [ ! -f context/company-profile.md ]; then
    cat > context/company-profile.md << 'EOF'
# Company Profile

## Overview
[Brief company description]

## Core Competencies
- [Competency 1]
- [Competency 2]
- [Competency 3]

## Strategic Goals
- [Goal 1]
- [Goal 2]
- [Goal 3]

## Available Resources
### Team
- [Team composition and skills]

### Budget
- [Budget constraints and allocation]

### Infrastructure
- [Existing infrastructure and capabilities]

## Constraints and Limitations
- [Constraint 1]
- [Constraint 2]
EOF
    print_success "Created context/company-profile.md template"
  else
    print_warning "context/company-profile.md already exists, skipping"
  fi

  if [ ! -f context/client-info.md ]; then
    cat > context/client-info.md << 'EOF'
# Client Information

## Client Profile
**Name**: [Client name or "Internal" for internal projects]
**Industry**: [Client's industry]
**Size**: [Company size]

## Background
[Client background and current situation]

## Goals and Objectives
- [Objective 1]
- [Objective 2]
- [Objective 3]

## Success Criteria
- [How client defines success]

## Constraints
- **Budget**: [Budget constraints]
- **Timeline**: [Timeline requirements]
- **Regulatory**: [Regulatory considerations]

## Stakeholders
- [Key stakeholder 1 and their role]
- [Key stakeholder 2 and their role]
EOF
    print_success "Created context/client-info.md template"
  else
    print_warning "context/client-info.md already exists, skipping"
  fi

  if [ ! -f context/industry-background.md ]; then
    cat > context/industry-background.md << 'EOF'
# Industry Background

## Industry Overview
[Overview of the industry sector]

## Current Trends
- [Trend 1]
- [Trend 2]
- [Trend 3]

## Regulatory Landscape
[Key regulations and regulatory bodies]

## Competitive Dynamics
[Competitive environment description]

## Technology Landscape
[Key technologies and innovation trends]

## Market Conditions
- **Market Size**: [TAM/SAM/SOM if known]
- **Growth Rate**: [CAGR]
- **Key Players**: [Major competitors]
EOF
    print_success "Created context/industry-background.md template"
  else
    print_warning "context/industry-background.md already exists, skipping"
  fi

  # Completion message
  print_header "Setup Complete!"

  echo "Next Steps:"
  echo "1. Edit .env and add your ANTHROPIC_API_KEY"
  echo "2. Customize config/project-config.yml with your project details"
  echo "3. Fill in context/ files with your project context"
  echo "4. Define sprints in config/sprint-config.yml"
  echo "5. Run validation: ./scripts/validate-structure.sh"
  echo ""
  echo "To create your first sprint:"
  echo "  /create-sprint \"Your Sprint Name\""
  echo ""
  echo "To execute a sprint:"
  echo "  /execute-sprint 01"
  echo ""
  print_success "Ready to start strategic research!"
}

# Run main function
main
