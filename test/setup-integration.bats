#!/usr/bin/env bats
# Integration tests for setup-template.sh with edge case inputs
#
# These tests actually run the setup script with various edge case inputs
# to ensure it handles special characters correctly

# Load test helpers
load 'test_helper/bats-support/load'
load 'test_helper/bats-assert/load'

# Setup function
setup() {
    # Create temporary test directory
    TEST_DIR="$(mktemp -d)"
    export TEST_DIR

    # Create a minimal template structure
    mkdir -p "$TEST_DIR/template"
    cd "$TEST_DIR/template"

    # Create minimal required structure
    mkdir -p .claude config context scripts templates

    # Create minimal config files with placeholders
    cat > config/project-config.yml <<EOF
project_name: {{PROJECT_NAME}}
company_name: {{COMPANY_NAME}}
client_name: {{CLIENT_NAME}}
industry: {{INDUSTRY}}
research_focus: {{RESEARCH_FOCUS}}
EOF

    cat > config/sprint-config.yml <<EOF
output_format: {{OUTPUT_FORMAT}}
detail_level: {{DETAIL_LEVEL}}
EOF

    # Create context examples
    cat > context/company-profile.md.example <<EOF
# {{COMPANY_NAME}} Company Profile
Industry: {{INDUSTRY}}
EOF

    cat > context/client-info.md.example <<EOF
# {{CLIENT_NAME}} Client Information
Industry: {{INDUSTRY}}
EOF

    cat > context/industry-background.md.example <<EOF
# {{INDUSTRY}} Industry Background
EOF

    # Create CLAUDE.md with placeholders
    cat > CLAUDE.md <<EOF
# Claude Code Guidelines for {{PROJECT_NAME}}
Company: {{COMPANY_NAME}}
Industry: {{INDUSTRY}}
EOF

    # Create .env.example
    touch .env.example

    # Create TEMPLATE_STRATEGY.md (will be removed by setup)
    touch TEMPLATE_STRATEGY.md

    # Copy the actual setup-template.sh script
    mkdir -p scripts
    cp "${BATS_TEST_DIRNAME}/../scripts/setup-template.sh" scripts/
    chmod +x scripts/setup-template.sh
}

# Teardown function
teardown() {
    # Clean up test directory
    if [ -n "$TEST_DIR" ] && [ -d "$TEST_DIR" ]; then
        rm -rf "$TEST_DIR"
    fi
}

# Helper function to run setup non-interactively
run_setup_non_interactive() {
    local project="$1"
    local company="$2"
    local client="$3"
    local industry="$4"
    local focus="${5:-comprehensive}"
    local output="${6:-all}"
    local detail="${7:-detailed}"

    # Create input file for non-interactive mode
    cat > "$TEST_DIR/input.txt" <<EOF
$project
$company
$client
10
$industry
10
$output
$detail
y
EOF

    # Run setup script with input
    run bash scripts/setup-template.sh < "$TEST_DIR/input.txt"
}

# Test: Setup with URLs in industry field
@test "setup-template.sh handles URLs in industry field" {
    cd "$TEST_DIR/template"

    # This is the exact scenario that caused the original bug
    INDUSTRY="https://www.linkedin.com/company/innova-technology-inc/"

    run_setup_non_interactive \
        "Test Project" \
        "Test Company" \
        "Test Client" \
        "$INDUSTRY"

    # Setup should succeed (exit 0)
    assert_success

    # Verify config files were created and contain the URL
    [ -f config/project-config.yml ]
    run grep "$INDUSTRY" config/project-config.yml
    assert_success
}

# Test: Setup with multiple URLs separated by dashes
@test "setup-template.sh handles multiple URLs in industry field" {
    cd "$TEST_DIR/template"

    INDUSTRY="https://www.example.com/one-https://www.example.com/two"

    run_setup_non_interactive \
        "Multi URL Project" \
        "Test Company" \
        "Test Client" \
        "$INDUSTRY"

    assert_success

    # Verify industry is in config
    run grep "$INDUSTRY" config/project-config.yml
    assert_success
}

# Test: Setup with special characters in company name
@test "setup-template.sh handles special characters in company name" {
    cd "$TEST_DIR/template"

    COMPANY="Company & Co. (Consulting)"

    run_setup_non_interactive \
        "Test Project" \
        "$COMPANY" \
        "Test Client" \
        "technology"

    assert_success

    # Verify company name is in config
    run grep "$COMPANY" config/project-config.yml
    assert_success
}

# Test: Setup with quotes in project name
@test "setup-template.sh handles quotes in project name" {
    cd "$TEST_DIR/template"

    PROJECT="Project \"Alpha\" Phase I"

    run_setup_non_interactive \
        "$PROJECT" \
        "Test Company" \
        "Test Client" \
        "technology"

    assert_success

    # Verify project name is in config
    run grep "Alpha" config/project-config.yml
    assert_success
}

# Test: Setup with forward slashes in client name
@test "setup-template.sh handles forward slashes in client name" {
    cd "$TEST_DIR/template"

    CLIENT="Client/Subsidiary/Division"

    run_setup_non_interactive \
        "Test Project" \
        "Test Company" \
        "$CLIENT" \
        "technology"

    assert_success

    # Verify client name is in config
    run grep "$CLIENT" config/project-config.yml
    assert_success
}

# Test: Setup with empty client name (should use default)
@test "setup-template.sh handles empty client name" {
    cd "$TEST_DIR/template"

    run_setup_non_interactive \
        "Test Project" \
        "Test Company" \
        "" \
        "technology"

    assert_success

    # Should default to "Internal"
    run grep "Internal" config/project-config.yml
    assert_success
}

# Test: Setup creates expected directory structure
@test "setup-template.sh creates required directories" {
    cd "$TEST_DIR/template"

    run_setup_non_interactive \
        "Test Project" \
        "Test Company" \
        "Test Client" \
        "technology"

    assert_success

    # Verify directories exist
    [ -d sprints ]
    [ -d temp ]
    [ -d reports ]
    [ -d context ]
}

# Test: Setup creates context files from examples
@test "setup-template.sh creates context files from examples" {
    cd "$TEST_DIR/template"

    run_setup_non_interactive \
        "Test Project" \
        "Test Company" \
        "Test Client" \
        "technology"

    assert_success

    # Verify context files were created
    [ -f context/company-profile.md ]
    [ -f context/client-info.md ]
    [ -f context/industry-background.md ]

    # Verify placeholders were replaced
    run grep "{{COMPANY_NAME}}" context/company-profile.md
    assert_failure  # Should NOT find placeholder

    run grep "Test Company" context/company-profile.md
    assert_success  # Should find replaced value
}

# Test: Setup removes template files
@test "setup-template.sh removes template-specific files" {
    cd "$TEST_DIR/template"

    run_setup_non_interactive \
        "Test Project" \
        "Test Company" \
        "Test Client" \
        "technology"

    assert_success

    # Template files should be removed
    [ ! -f TEMPLATE_STRATEGY.md ]
    [ ! -d templates/ ]
}

# Test: Setup creates .env from .env.example
@test "setup-template.sh creates .env from example" {
    cd "$TEST_DIR/template"

    run_setup_non_interactive \
        "Test Project" \
        "Test Company" \
        "Test Client" \
        "technology"

    assert_success

    # .env should be created
    [ -f .env ]
}

# Test: Setup customizes CLAUDE.md
@test "setup-template.sh customizes CLAUDE.md" {
    cd "$TEST_DIR/template"

    PROJECT="My Project"
    COMPANY="My Company"
    INDUSTRY="technology"

    run_setup_non_interactive \
        "$PROJECT" \
        "$COMPANY" \
        "Test Client" \
        "$INDUSTRY"

    assert_success

    # Verify CLAUDE.md was customized
    [ -f CLAUDE.md ]

    run grep "{{PROJECT_NAME}}" CLAUDE.md
    assert_failure  # Should NOT find placeholder

    run grep "$PROJECT" CLAUDE.md
    assert_success  # Should find replaced value
}

# Test: Setup handles UTF-8 characters
@test "setup-template.sh handles UTF-8 characters in inputs" {
    cd "$TEST_DIR/template"

    COMPANY="Société Française™"

    run_setup_non_interactive \
        "Test Project" \
        "$COMPANY" \
        "Test Client" \
        "technology"

    assert_success

    # Verify UTF-8 is preserved
    run grep "Société" config/project-config.yml
    assert_success
}

# Test: Stress test with all edge cases combined
@test "setup-template.sh handles all edge cases combined" {
    cd "$TEST_DIR/template"

    PROJECT="Project \"Alpha\" & Beta (Phase I/II)"
    COMPANY="Company & Co. Ltd.™"
    CLIENT="Client/Division/Subsidiary"
    INDUSTRY="https://example.com/tech-https://example.com/saas"

    run_setup_non_interactive \
        "$PROJECT" \
        "$COMPANY" \
        "$CLIENT" \
        "$INDUSTRY"

    assert_success

    # Verify all values are in config
    run grep "Alpha" config/project-config.yml
    assert_success

    run grep "Company & Co" config/project-config.yml
    assert_success

    run grep "Client/Division" config/project-config.yml
    assert_success

    run grep "https://example.com" config/project-config.yml
    assert_success
}

# Test: Verify no sed errors in output
@test "setup-template.sh produces no sed errors" {
    cd "$TEST_DIR/template"

    INDUSTRY="https://www.linkedin.com/company/test/"

    run_setup_non_interactive \
        "Test Project" \
        "Test Company" \
        "Test Client" \
        "$INDUSTRY"

    assert_success

    # Output should NOT contain sed error messages
    refute_output --partial "bad flag in substitute command"
    refute_output --partial "sed: "
}

# Test: Verify config files are valid YAML after setup
@test "setup-template.sh produces valid YAML config files" {
    cd "$TEST_DIR/template"

    run_setup_non_interactive \
        "Test Project" \
        "Test Company" \
        "Test Client" \
        "technology"

    assert_success

    # If yamllint is available, validate YAML
    if command -v yamllint &> /dev/null; then
        run yamllint config/project-config.yml
        assert_success
    else
        skip "yamllint not available"
    fi
}
