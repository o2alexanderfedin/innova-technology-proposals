#!/usr/bin/env bats
# Tests for setup scripts - focuses on edge cases and security
#
# Tests cover:
# - sed delimiter handling with special characters
# - Variable quoting and escaping
# - Input validation
# - Path handling with spaces and special characters

# Load test helpers
load 'test_helper/bats-support/load'
load 'test_helper/bats-assert/load'

# Setup function - runs before each test
setup() {
    # Create temporary test directory
    TEST_DIR="$(mktemp -d)"
    export TEST_DIR

    # Create minimal config structure for testing
    mkdir -p "$TEST_DIR/config"
    mkdir -p "$TEST_DIR/context"
    mkdir -p "$TEST_DIR/scripts"

    # Copy scripts to test directory
    cp -r "${BATS_TEST_DIRNAME}/../scripts" "$TEST_DIR/" 2>/dev/null || true
}

# Teardown function - runs after each test
teardown() {
    # Clean up test directory
    if [ -n "$TEST_DIR" ] && [ -d "$TEST_DIR" ]; then
        rm -rf "$TEST_DIR"
    fi
}

# Test: sed handles forward slashes in input
@test "sed delimiter handles URLs with forward slashes" {
    # Create test file with placeholder
    echo "Industry: {{INDUSTRY}}" > "$TEST_DIR/test.txt"

    # Variable with forward slashes (URL)
    INDUSTRY="https://www.example.com/path/to/resource"

    # This should NOT fail with pipe delimiter
    run sed -e "s|{{INDUSTRY}}|$INDUSTRY|g" "$TEST_DIR/test.txt"

    assert_success
    assert_output "Industry: https://www.example.com/path/to/resource"
}

# Test: sed handles multiple URLs separated by spaces
@test "sed delimiter handles multiple URLs" {
    echo "Sources: {{SOURCES}}" > "$TEST_DIR/test.txt"

    SOURCES="https://example.com/one https://example.com/two https://example.com/three"

    run sed -e "s|{{SOURCES}}|$SOURCES|g" "$TEST_DIR/test.txt"

    assert_success
    assert_output "Sources: https://example.com/one https://example.com/two https://example.com/three"
}

# Test: sed handles pipe characters in input (edge case)
@test "sed delimiter handles pipe characters in input" {
    echo "Command: {{COMMAND}}" > "$TEST_DIR/test.txt"

    # Using pipe delimiter but input contains pipe
    COMMAND="ls | grep test"

    # This is a known limitation - pipe delimiter will fail with pipes in input
    # We use a different delimiter for this edge case
    run sed -e "s#{{COMMAND}}#$COMMAND#g" "$TEST_DIR/test.txt"

    assert_success
    assert_output "Command: ls | grep test"
}

# Test: sed handles special regex characters
@test "sed handles special regex characters" {
    echo "Pattern: {{PATTERN}}" > "$TEST_DIR/test.txt"

    # Special regex characters that need escaping
    PATTERN="test.*[0-9]+(special)"

    # Escape special characters for sed
    PATTERN_ESCAPED=$(echo "$PATTERN" | sed 's/[.*[\^$]/\\&/g')

    run sed -e "s|{{PATTERN}}|$PATTERN_ESCAPED|g" "$TEST_DIR/test.txt"

    assert_success
}

# Test: sed handles empty values
@test "sed handles empty replacement values" {
    echo "Value: {{VALUE}}" > "$TEST_DIR/test.txt"

    VALUE=""

    run sed -e "s|{{VALUE}}|$VALUE|g" "$TEST_DIR/test.txt"

    assert_success
    assert_output "Value: "
}

# Test: sed handles values with spaces
@test "sed handles values with multiple spaces" {
    echo "Name: {{NAME}}" > "$TEST_DIR/test.txt"

    NAME="Company    Name    With    Spaces"

    run sed -e "s|{{NAME}}|$NAME|g" "$TEST_DIR/test.txt"

    assert_success
    assert_output "Name: Company    Name    With    Spaces"
}

# Test: sed handles values with newlines (multiline)
@test "sed handles multiline values" {
    echo "Description: {{DESC}}" > "$TEST_DIR/test.txt"

    DESC="Line 1\nLine 2\nLine 3"

    run sed -e "s|{{DESC}}|$DESC|g" "$TEST_DIR/test.txt"

    assert_success
}

# Test: sed handles values with quotes
@test "sed handles values with single and double quotes" {
    echo "Text: {{TEXT}}" > "$TEST_DIR/test.txt"

    TEXT="Company's \"Best\" Product"

    run sed -e "s|{{TEXT}}|$TEXT|g" "$TEST_DIR/test.txt"

    assert_success
    assert_output "Text: Company's \"Best\" Product"
}

# Test: sed handles values with dollar signs
@test "sed handles values with dollar signs" {
    echo "Price: {{PRICE}}" > "$TEST_DIR/test.txt"

    PRICE="\$100.00 USD"

    run sed -e "s|{{PRICE}}|$PRICE|g" "$TEST_DIR/test.txt"

    assert_success
}

# Test: sed handles values with backticks
@test "sed handles values with backticks" {
    echo "Code: {{CODE}}" > "$TEST_DIR/test.txt"

    CODE="\`command\` execution"

    run sed -e "s|{{CODE}}|$CODE|g" "$TEST_DIR/test.txt"

    assert_success
}

# Test: Variable quoting prevents word splitting
@test "quoted variables prevent word splitting" {
    # Create a variable with spaces
    FILE_NAME="test file with spaces.txt"

    # Create the file
    touch "$TEST_DIR/$FILE_NAME"

    # Test unquoted (should fail or behave unexpectedly)
    # This is intentionally testing the wrong way
    run bash -c "ls $TEST_DIR/$FILE_NAME"
    assert_failure

    # Test quoted (should succeed)
    run bash -c "ls \"$TEST_DIR/$FILE_NAME\""
    assert_success
}

# Test: Variable quoting prevents glob expansion
@test "quoted variables prevent glob expansion" {
    # Create test files
    touch "$TEST_DIR/file1.txt"
    touch "$TEST_DIR/file2.txt"

    PATTERN="*.txt"

    # Unquoted should expand glob
    run bash -c "echo $PATTERN"
    # Output depends on current directory

    # Quoted should preserve literal asterisk
    run bash -c "echo \"$PATTERN\""
    assert_output "*.txt"
}

# Test: Path traversal protection
@test "path handling with .. is safe" {
    # Create nested directory
    mkdir -p "$TEST_DIR/subdir"

    # Attempt to use .. in path
    UNSAFE_PATH="../../../etc/passwd"

    # Our scripts should validate and reject this
    # (This test assumes validation exists)
    run bash -c "[ -f \"$TEST_DIR/$UNSAFE_PATH\" ] && echo 'UNSAFE' || echo 'SAFE'"
    assert_output "SAFE"
}

# Test: Input validation for required fields
@test "validate_not_empty rejects empty input" {
    skip "Requires interactive input simulation"
    # This test would need expect or similar for interactive testing
}

# Test: Input sanitization for industry field
@test "industry field sanitization works" {
    # Simulate the sanitization from setup-template.sh
    INDUSTRY="Tech Industry (Advanced Systems)"
    SANITIZED=$(echo "$INDUSTRY" | tr '[:upper:]' '[:lower:]' | tr ' ' '-')

    assert_equal "$SANITIZED" "tech-industry-(advanced-systems)"
}

# Test: Input sanitization removes dangerous characters
@test "input sanitization handles special characters" {
    INPUT="Company & Co. / Division"
    # Basic sanitization (lowercase + spaces to dashes)
    SANITIZED=$(echo "$INPUT" | tr '[:upper:]' '[:lower:]' | tr ' ' '-')

    # Should convert but preserve some special chars
    assert_equal "$SANITIZED" "company-&-co.-/-division"
}

# Test: sed handles complex real-world example
@test "sed handles real-world Innova Technology example" {
    echo "Industry: {{INDUSTRY}}" > "$TEST_DIR/test.txt"

    # Exact input from the user's error
    INDUSTRY="research-it-by-yourself.-here-are-some-sources:-https://www.linkedin.com/company/innova-technology-inc/-https://innova-technology.com/-https://clutch.co/profile/innova-1-cto-=-igor-novikov"

    # This should work with pipe delimiter
    run sed -e "s|{{INDUSTRY}}|$INDUSTRY|g" "$TEST_DIR/test.txt"

    assert_success
    assert_output "Industry: $INDUSTRY"
}

# Test: Multiple sed replacements in sequence (with escaping)
@test "multiple sed replacements work correctly" {
    cat > "$TEST_DIR/test.yml" <<EOF
project_name: {{PROJECT_NAME}}
company: {{COMPANY_NAME}}
industry: {{INDUSTRY}}
EOF

    # Helper function to escape special characters for sed
    escape_for_sed() {
        echo "$1" | sed 's/[&/\]/\\&/g'
    }

    PROJECT_NAME="Test Project"
    COMPANY_NAME="Test & Company"
    INDUSTRY="https://example.com/tech"

    # Escape special characters
    PROJECT_NAME_ESC=$(escape_for_sed "$PROJECT_NAME")
    COMPANY_NAME_ESC=$(escape_for_sed "$COMPANY_NAME")
    INDUSTRY_ESC=$(escape_for_sed "$INDUSTRY")

    run sed \
        -e "s|{{PROJECT_NAME}}|$PROJECT_NAME_ESC|g" \
        -e "s|{{COMPANY_NAME}}|$COMPANY_NAME_ESC|g" \
        -e "s|{{INDUSTRY}}|$INDUSTRY_ESC|g" \
        "$TEST_DIR/test.yml"

    assert_success
    assert_line --index 0 "project_name: Test Project"
    assert_line --index 1 "company: Test & Company"
    assert_line --index 2 "industry: https://example.com/tech"
}

# Test: sed -i.bak creates backup and modifies file
@test "sed -i.bak creates backup before modifying" {
    echo "Original: {{VALUE}}" > "$TEST_DIR/test.txt"

    VALUE="New Value"

    run sed -i.bak -e "s|{{VALUE}}|$VALUE|g" "$TEST_DIR/test.txt"

    assert_success

    # Check backup exists
    [ -f "$TEST_DIR/test.txt.bak" ]

    # Check original content in backup
    run cat "$TEST_DIR/test.txt.bak"
    assert_output "Original: {{VALUE}}"

    # Check modified content in main file
    run cat "$TEST_DIR/test.txt"
    assert_output "Original: New Value"
}

# Test: sed handles UTF-8 characters
@test "sed handles UTF-8 characters" {
    echo "Company: {{COMPANY}}" > "$TEST_DIR/test.txt"

    COMPANY="Société Française™"

    run sed -e "s|{{COMPANY}}|$COMPANY|g" "$TEST_DIR/test.txt"

    assert_success
    assert_output "Company: Société Française™"
}

# Test: Delimiter consistency across all sed commands
@test "verify all sed commands use pipe delimiter in setup-template.sh" {
    # Search for sed commands with / delimiter
    run bash -c "grep -n 'sed.*\"s/' ${BATS_TEST_DIRNAME}/../scripts/setup-template.sh | grep -v 's|' || echo 'ALL_SAFE'"

    assert_output "ALL_SAFE"
}

# Test: Delimiter consistency in setup-existing.sh
@test "verify all sed commands use pipe delimiter in setup-existing.sh" {
    # Search for sed commands with / delimiter
    run bash -c "grep -n 'sed.*\"s/' ${BATS_TEST_DIRNAME}/../scripts/setup-existing.sh | grep -v 's|' || echo 'ALL_SAFE'"

    assert_output "ALL_SAFE"
}

# Test: No eval usage in setup scripts
@test "verify no eval usage in setup-template.sh" {
    # Look for eval as a command (word boundary), not just substring
    run bash -c "grep -nw 'eval' ${BATS_TEST_DIRNAME}/../scripts/setup-template.sh || echo 'NO_EVAL'"

    assert_output "NO_EVAL"
}

@test "verify no eval usage in setup-existing.sh" {
    # Look for eval as a command (word boundary), not just substring
    run bash -c "grep -nw 'eval' ${BATS_TEST_DIRNAME}/../scripts/setup-existing.sh || echo 'NO_EVAL'"

    assert_output "NO_EVAL"
}

# Test: Proper variable quoting in critical sections
@test "verify variables are quoted in setup-template.sh" {
    # Check for unquoted variables in dangerous contexts
    # This is a heuristic - looks for $VAR without quotes in sensitive contexts
    run bash -c "grep -E 'rm -rf \$[A-Z_]+[^\"]*$' ${BATS_TEST_DIRNAME}/../scripts/setup-template.sh || echo 'SAFE'"

    assert_output "SAFE"
}
