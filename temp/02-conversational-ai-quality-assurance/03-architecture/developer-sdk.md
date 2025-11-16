# Developer SDK Architecture

**Research Date**: January 2025
**Sprint**: 02 - Conversational AI Quality Assurance
**Task**: 03 - Solution Architecture Design
**Researcher**: Solution Architect Skill

## Executive Summary

The Hapyy Conversational QA Developer SDK transforms chatbot testing from manual, subjective evaluation to automated, mathematical validation integrated directly into the software development lifecycle. This SDK enables developers to write test specifications for conversation flows, validate chatbot responses against business rules before deployment, and integrate validation into CI/CD pipelines for continuous quality assurance. The SDK's business value is substantial: reduce QA time from weeks to hours, catch errors in development (where fixes cost $100) rather than production (where fixes cost $10,000+), and enable test-driven development for conversational AI (write conversation tests first, implement chatbot logic second).

The SDK provides multi-language support (Python, Node.js, Java) with idiomatic APIs, conversation specification DSL for readable test definitions, and seamless integration with popular testing frameworks (pytest, Jest, JUnit). Developers can run validation locally during development, in staging environments for pre-release validation, and in CI/CD pipelines for automated quality gates. The architecture prioritizes developer experience: simple installation, minimal configuration, clear error messages, and comprehensive documentation.

## Key Design Decisions

- **Multi-Language Support**: Python (primary), Node.js (secondary), Java (enterprise), with consistent API design across languages
- **Conversation Specification DSL**: YAML-based format for defining conversation flows with expected outcomes, balancing readability and expressiveness
- **Testing Framework Integration**: Native adapters for pytest, Jest, JUnit to leverage existing testing infrastructure
- **Local and Remote Validation**: SDK can validate locally (fast, limited knowledge base) or remotely (comprehensive, cloud-based validation)
- **CLI Tool**: Command-line interface for ad-hoc validation and CI/CD integration without code changes
- **IDE Extensions**: VS Code and PyCharm plugins for inline validation and autocomplete
- **Caching Strategy**: Aggressive local caching of validation results to minimize API calls and reduce latency
- **Error-First Design**: Detailed error messages with actionable suggestions for fixing validation failures
- **Open Source Core**: Core SDK open-sourced on GitHub to drive adoption, with premium features (advanced knowledge bases) behind API key

## SDK Architecture Overview

### Component Structure

**Textual Component Diagram**:

```
┌─────────────────────────────────────────────────────────────────┐
│                        APPLICATION LAYER                         │
│  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────┐  │
│  │  Developer Code  │  │   Test Specs     │  │  CI/CD Jobs  │  │
│  │   (app.py)       │  │ (conversation    │  │  (.github/   │  │
│  │                  │  │  .yml files)     │  │   workflows) │  │
│  └────────┬─────────┘  └────────┬─────────┘  └───────┬──────┘  │
└───────────┼─────────────────────┼────────────────────┼─────────┘
            │                     │                    │
            │ import              │ pytest discover    │ CLI invoke
            │                     │                    │
┌───────────┴─────────────────────┴────────────────────┴─────────┐
│                      HAPYY SDK LAYER                             │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │              Language-Specific Wrapper                    │  │
│  │   ┌──────────────┐  ┌─────────────┐  ┌──────────────┐   │  │
│  │   │ Python SDK   │  │ Node.js SDK │  │  Java SDK    │   │  │
│  │   │ (hapyy-qa)   │  │ (@hapyy/qa) │  │ (hapyy-qa)   │   │  │
│  │   └──────┬───────┘  └──────┬──────┘  └──────┬───────┘   │  │
│  └──────────┼──────────────────┼─────────────────┼──────────┘  │
│             │                  │                 │              │
│  ┌──────────┴──────────────────┴─────────────────┴──────────┐  │
│  │                   Core SDK Engine (Python)                │  │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────────────┐  │  │
│  │  │ Spec Parser│  │ Validator  │  │  Result Formatter  │  │  │
│  │  │ (YAML→AST) │  │ Orchestrate│  │  (JUnit XML, JSON) │  │  │
│  │  └────────────┘  └────────────┘  └────────────────────┘  │  │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────────────┐  │  │
│  │  │   Cache    │  │  API Client│  │  Error Explainer   │  │  │
│  │  │  (SQLite)  │  │ (HTTP/gRPC)│  │  (Suggestions)     │  │  │
│  │  └────────────┘  └────────────┘  └────────────────────┘  │  │
│  └──────────────────────────┬───────────────────────────────┘  │
└─────────────────────────────┼──────────────────────────────────┘
                              │
                    [Local or Remote?]
                              │
                ┌─────────────┴─────────────┐
                │                           │
         ┌──────▼──────┐            ┌───────▼────────┐
         │    LOCAL    │            │     REMOTE     │
         │  VALIDATION │            │   VALIDATION   │
         │             │            │                │
         │ ┌─────────┐ │            │  Hapyy Cloud   │
         │ │  Basic  │ │            │  Validation    │
         │ │ Rules   │ │            │  API           │
         │ │ Engine  │ │            │                │
         │ └─────────┘ │            │ (Full KB,      │
         │             │            │  SMT Solver)   │
         └─────────────┘            └────────────────┘
              ↓                            ↓
         Fast (<50ms)               Comprehensive (<500ms)
         No API key required        Requires API key
```

### Core SDK Components

**1. Specification Parser**:
- **Input**: YAML conversation test specifications
- **Output**: Abstract Syntax Tree (AST) representing conversation flow
- **Validation**: Schema validation, syntax checking, semantic analysis
- **Features**: Variable substitution, conditional logic, loops for parameterized tests

**2. Validation Orchestrator**:
- **Responsibility**: Coordinate validation workflow
- **Functions**:
  - Parse conversation specifications
  - Execute validation requests (local or remote)
  - Aggregate results from multiple validations
  - Format results for testing frameworks

**3. API Client**:
- **Protocols**: REST (HTTP/2) for cloud deployment, gRPC for low-latency
- **Features**:
  - Automatic retry with exponential backoff
  - Request batching (multiple conversations in single API call)
  - Streaming for real-time validation
  - Circuit breaker for graceful degradation

**4. Cache Layer**:
- **Storage**: SQLite database for local caching
- **Strategy**: Cache validation results keyed by conversation hash
- **TTL**: Default 24 hours, configurable per knowledge base version
- **Invalidation**: Automatic invalidation on knowledge base updates

**5. Result Formatter**:
- **Formats**: JUnit XML (Jenkins, CircleCI), JSON (custom reporting), TAP (Test Anything Protocol)
- **Integrations**: pytest, Jest, JUnit, Mocha, Jasmine
- **Features**: Detailed error messages, proof/counterexample display, suggestions

**6. Error Explainer**:
- **Input**: Validation failure with counterexample from SMT solver
- **Output**: Human-readable explanation with actionable suggestions
- **Example**:
  - Input: `Expected premium $347, bot stated $247`
  - Output: `Premium calculation error: Bot undercharged by $100. Correct formula: base_rate($285) + age_factor(45y: $62) = $347. Check pricing table version.`

## Python SDK

### Installation

**Package Name**: `hapyy-conversational-qa`

**Installation**:
```bash
pip install hapyy-conversational-qa
```

**Dependencies**:
- Python 3.9+
- `pyyaml` (conversation spec parsing)
- `requests` (API client)
- `pytest` (optional, for testing framework integration)

### Configuration

**API Key Setup**:
```bash
export HAPYY_API_KEY="hpyy_sk_abc123..."
```

Or in code:
```python
from hapyy_qa import HapyyValidator

validator = HapyyValidator(api_key="hpyy_sk_abc123...")
```

**Configuration File** (`.hapyyrc.yml`):
```yaml
api_key: ${HAPYY_API_KEY}
endpoint: https://validation.hapyy.ai
validation_mode: remote  # or 'local' for basic validation
cache_enabled: true
cache_ttl: 86400  # 24 hours
timeout: 1000  # milliseconds
knowledge_base:
  client_id: my_company_healthco
  version: latest  # or specific version like '2024-Q4'
```

### Basic Usage

**Validate Single Conversation**:
```python
from hapyy_qa import HapyyValidator

validator = HapyyValidator()

result = validator.validate(
    user_query="What is the monthly premium for Plan A with $500 deductible for age 45?",
    bot_response="The monthly premium would be $347.",
    context={
        "user_profile": {"age": 45, "location": "California"},
        "intent": "pricing_query"
    }
)

if result.is_valid:
    print("✓ Response validated successfully")
else:
    print(f"✗ Validation failed: {result.explanation}")
    print(f"  Counterexample: {result.counterexample}")
```

**Output** (validation failure):
```
✗ Validation failed: Premium calculation error
  Expected: $347
  Bot stated: $247
  Error: Undercharged by $100

  Counterexample:
    Correct formula: base_rate($285) + age_factor(45y: $62) = $347
    Bot used: Unknown calculation resulting in $247

  Suggestion: Verify pricing table version and age factor calculation
```

### Conversation Specification DSL

**File Format**: YAML for readability and version control compatibility

**Example Specification** (`tests/conversations/pricing_quote.yml`):
```yaml
# Conversation test: Insurance pricing quote
name: "Health Insurance Premium Quote - Plan A"
description: "Validate premium calculation for 45-year-old, Plan A, $500 deductible"

knowledge_base:
  client_id: healthco
  version: 2024-Q4

conversation:
  - role: user
    content: "I'm looking for health insurance."

  - role: assistant
    content: "I'd be happy to help! Are you looking for individual or family coverage?"

  - role: user
    content: "Individual coverage for myself. I'm 45 years old in California."

  - role: assistant
    content: "Great! What deductible level are you considering?"

  - role: user
    content: "I'd like to see pricing for Plan A with a $500 deductible."

  - role: assistant
    content: "The monthly premium for Plan A with a $500 deductible would be $347."
    validate:
      entities:
        plan: "Plan A"
        deductible: 500
        premium: 347
      business_rules:
        - pricing_formula_correct
        - deductible_available_for_plan
        - age_factor_applied
      compliance:
        - aca_compliant
        - no_discrimination

expectations:
  validation_status: VALID
  confidence: 1.0
  entities_extracted:
    - plan
    - deductible
    - premium
```

**Advanced Specification** (parameterized testing):
```yaml
name: "Premium Quote - Multiple Ages"
description: "Test premium calculation across age ranges"

parameters:
  ages: [25, 35, 45, 55, 65]
  plans: ["Plan A", "Plan B", "Plan C"]
  deductibles: [500, 1000, 2500]

template:
  conversation:
    - role: user
      content: "What's the premium for {{plan}} with ${{deductible}} deductible for age {{age}}?"

    - role: assistant
      content: "The monthly premium is ${{expected_premium}}."
      validate:
        entities:
          plan: "{{plan}}"
          deductible: {{deductible}}
          age: {{age}}
          premium: {{expected_premium}}
        business_rules:
          - pricing_formula_correct

  expectations:
    validation_status: VALID

# Generate expected premiums from knowledge base
expected_premiums:
  - {age: 25, plan: "Plan A", deductible: 500, premium: 285}
  - {age: 35, plan: "Plan A", deductible: 500, premium: 310}
  - {age: 45, plan: "Plan A", deductible: 500, premium: 347}
  # ... etc
```

### pytest Integration

**Test File** (`tests/test_conversations.py`):
```python
import pytest
from hapyy_qa import HapyyValidator

validator = HapyyValidator()

@pytest.mark.hapyy
def test_pricing_quote_plan_a():
    """Test premium calculation for Plan A"""
    result = validator.validate_spec("tests/conversations/pricing_quote.yml")
    assert result.is_valid, result.explanation

@pytest.mark.hapyy
@pytest.mark.parametrize("age,expected_premium", [
    (25, 285),
    (35, 310),
    (45, 347),
    (55, 405),
])
def test_pricing_quote_age_factors(age, expected_premium):
    """Test premium calculation across age ranges"""
    result = validator.validate(
        user_query=f"What's the premium for Plan A, $500 deductible, age {age}?",
        bot_response=f"The monthly premium is ${expected_premium}.",
        context={"user_profile": {"age": age}, "intent": "pricing_query"}
    )
    assert result.is_valid, f"Age {age}: {result.explanation}"

@pytest.mark.hapyy
def test_conversation_directory():
    """Validate all conversation specs in directory"""
    results = validator.validate_directory("tests/conversations/")

    failures = [r for r in results if not r.is_valid]
    if failures:
        for failure in failures:
            print(f"FAILED: {failure.spec_name}")
            print(f"  {failure.explanation}")
        pytest.fail(f"{len(failures)}/{len(results)} conversations failed validation")
```

**Running Tests**:
```bash
# Run all Hapyy validation tests
pytest -m hapyy

# Run with verbose output
pytest -m hapyy -v

# Generate JUnit XML report
pytest -m hapyy --junitxml=validation-results.xml

# Run in parallel (faster)
pytest -m hapyy -n 4
```

**pytest Plugin**:

The SDK provides a pytest plugin for automatic test discovery and reporting.

**Installation**: Automatically installed with `hapyy-conversational-qa[pytest]`

**Configuration** (`pytest.ini`):
```ini
[pytest]
markers =
    hapyy: Hapyy conversational QA validation tests

hapyy_config =
    api_key = ${HAPYY_API_KEY}
    endpoint = https://validation.hapyy.ai
    knowledge_base = healthco
```

**Auto-Discovery**: Pytest automatically discovers `.yml` files in `tests/conversations/` and runs them as tests.

### CLI Tool

**Installation**: Included with SDK

**Command**: `hapyy-qa`

**Validate Single Conversation**:
```bash
hapyy-qa validate \
  --query "What's the premium for Plan A, $500 deductible, age 45?" \
  --response "The monthly premium is $347." \
  --client-id healthco
```

**Output**:
```
✓ Validation PASSED
  Confidence: 1.0
  Latency: 287ms

  Entities Validated:
    - plan: Plan A
    - deductible: $500
    - premium: $347

  Business Rules Checked:
    ✓ pricing_formula_correct
    ✓ deductible_available_for_plan
    ✓ age_factor_applied
```

**Validate Conversation Spec**:
```bash
hapyy-qa validate-spec tests/conversations/pricing_quote.yml
```

**Validate Directory**:
```bash
hapyy-qa validate-dir tests/conversations/ --output-format junit
```

**Generate Test Report**:
```bash
hapyy-qa report \
  --input validation-results.json \
  --output validation-report.html \
  --format html
```

**CI/CD Integration**:
```bash
# Exit code 0 if all validations pass, 1 if any fail
hapyy-qa validate-dir tests/conversations/ || exit 1
```

## Node.js SDK

### Installation

**Package Name**: `@hapyy/conversational-qa`

**Installation**:
```bash
npm install --save-dev @hapyy/conversational-qa
```

Or with Yarn:
```bash
yarn add --dev @hapyy/conversational-qa
```

### Basic Usage

**TypeScript/JavaScript**:
```typescript
import { HapyyValidator } from '@hapyy/conversational-qa';

const validator = new HapyyValidator({
  apiKey: process.env.HAPYY_API_KEY,
  knowledgeBase: { clientId: 'healthco', version: 'latest' }
});

const result = await validator.validate({
  userQuery: "What's the premium for Plan A with $500 deductible for age 45?",
  botResponse: "The monthly premium would be $347.",
  context: {
    userProfile: { age: 45, location: 'California' },
    intent: 'pricing_query'
  }
});

if (result.isValid) {
  console.log('✓ Response validated successfully');
} else {
  console.error('✗ Validation failed:', result.explanation);
  console.error('  Counterexample:', result.counterexample);
}
```

### Jest Integration

**Test File** (`__tests__/conversations.test.ts`):
```typescript
import { HapyyValidator } from '@hapyy/conversational-qa';

const validator = new HapyyValidator();

describe('Conversation Validation', () => {
  it('should validate pricing quote for Plan A', async () => {
    const result = await validator.validateSpec('tests/conversations/pricing_quote.yml');
    expect(result.isValid).toBe(true);
  });

  it.each([
    [25, 285],
    [35, 310],
    [45, 347],
    [55, 405],
  ])('should calculate correct premium for age %i', async (age, expectedPremium) => {
    const result = await validator.validate({
      userQuery: `What's the premium for Plan A, $500 deductible, age ${age}?`,
      botResponse: `The monthly premium is $${expectedPremium}.`,
      context: { userProfile: { age }, intent: 'pricing_query' }
    });

    expect(result.isValid).toBe(true);
  });

  it('should fail validation for incorrect premium', async () => {
    const result = await validator.validate({
      userQuery: "What's the premium for Plan A, $500 deductible, age 45?",
      botResponse: "The monthly premium is $247.",  // WRONG (should be $347)
      context: { userProfile: { age: 45 }, intent: 'pricing_query' }
    });

    expect(result.isValid).toBe(false);
    expect(result.explanation).toContain('Premium calculation error');
    expect(result.counterexample.expectedPremium).toBe(347);
    expect(result.counterexample.statedPremium).toBe(247);
  });
});
```

**Jest Configuration** (`jest.config.js`):
```javascript
module.exports = {
  preset: 'ts-jest',
  testEnvironment: 'node',
  setupFilesAfterEnv: ['@hapyy/conversational-qa/jest-setup'],
  testMatch: ['**/__tests__/**/*.test.ts'],
};
```

### GitHub Actions Integration

**Workflow File** (`.github/workflows/validate-conversations.yml`):
```yaml
name: Validate Conversations

on:
  pull_request:
    paths:
      - 'src/chatbot/**'
      - 'tests/conversations/**'
  push:
    branches: [main, develop]

jobs:
  validate:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v3

      - name: Setup Node.js
        uses: actions/setup-node@v3
        with:
          node-version: '18'
          cache: 'npm'

      - name: Install dependencies
        run: npm ci

      - name: Run conversation validation
        env:
          HAPYY_API_KEY: ${{ secrets.HAPYY_API_KEY }}
        run: npm test -- --testPathPattern=conversations

      - name: Upload test results
        if: always()
        uses: actions/upload-artifact@v3
        with:
          name: validation-results
          path: validation-results.xml

      - name: Comment PR with results
        if: github.event_name == 'pull_request'
        uses: hapyy/validation-comment-action@v1
        with:
          results-file: validation-results.xml
```

**Pull Request Comment** (automatically posted):
```markdown
## 🤖 Hapyy Conversation Validation Results

✅ **12 conversations validated successfully**
❌ **2 conversations failed validation**

### Failed Validations

1. **Premium Quote - Plan B**
   - Error: Premium calculation incorrect
   - Expected: $425
   - Bot stated: $325
   - Fix: Update Plan B pricing table to 2024-Q4 version

2. **Eligibility Check - Pre-existing Condition**
   - Error: Policy violation
   - Issue: Bot approved coverage for excluded condition (active cancer)
   - Fix: Review eligibility rules for pre-existing conditions

[View detailed report →](https://validation.hapyy.ai/reports/pr-1234)
```

## Java SDK

### Installation

**Maven** (`pom.xml`):
```xml
<dependency>
  <groupId>ai.hapyy</groupId>
  <artifactId>conversational-qa</artifactId>
  <version>1.0.0</version>
  <scope>test</scope>
</dependency>
```

**Gradle** (`build.gradle`):
```groovy
testImplementation 'ai.hapyy:conversational-qa:1.0.0'
```

### Basic Usage

**Java**:
```java
import ai.hapyy.qa.HapyyValidator;
import ai.hapyy.qa.ValidationResult;

public class ConversationTest {
    private static final HapyyValidator validator = new HapyyValidator.Builder()
        .apiKey(System.getenv("HAPYY_API_KEY"))
        .knowledgeBase("healthco", "latest")
        .build();

    public static void main(String[] args) {
        ValidationResult result = validator.validate(
            "What's the premium for Plan A with $500 deductible for age 45?",
            "The monthly premium would be $347.",
            Map.of("user_profile", Map.of("age", 45), "intent", "pricing_query")
        );

        if (result.isValid()) {
            System.out.println("✓ Response validated successfully");
        } else {
            System.err.println("✗ Validation failed: " + result.getExplanation());
            System.err.println("  Counterexample: " + result.getCounterexample());
        }
    }
}
```

### JUnit 5 Integration

**Test Class**:
```java
import ai.hapyy.qa.HapyyValidator;
import ai.hapyy.qa.annotations.HapyyTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import static org.junit.jupiter.api.Assertions.*;

@HapyyTest
public class PricingConversationTest {
    private final HapyyValidator validator = new HapyyValidator.Builder()
        .apiKey(System.getenv("HAPYY_API_KEY"))
        .build();

    @Test
    public void testPricingQuotePlanA() {
        var result = validator.validateSpec("tests/conversations/pricing_quote.yml");
        assertTrue(result.isValid(), result.getExplanation());
    }

    @ParameterizedTest
    @CsvSource({
        "25, 285",
        "35, 310",
        "45, 347",
        "55, 405"
    })
    public void testPricingAcrossAges(int age, int expectedPremium) {
        var result = validator.validate(
            String.format("What's the premium for Plan A, $500 deductible, age %d?", age),
            String.format("The monthly premium is $%d.", expectedPremium),
            Map.of("user_profile", Map.of("age", age), "intent", "pricing_query")
        );

        assertTrue(result.isValid(),
            String.format("Age %d: %s", age, result.getExplanation()));
    }
}
```

## CI/CD Integration Examples

### Jenkins Pipeline

**Jenkinsfile**:
```groovy
pipeline {
    agent any

    environment {
        HAPYY_API_KEY = credentials('hapyy-api-key')
    }

    stages {
        stage('Setup') {
            steps {
                sh 'pip install hapyy-conversational-qa'
            }
        }

        stage('Validate Conversations') {
            steps {
                sh 'hapyy-qa validate-dir tests/conversations/ --output-format junit'
            }
        }

        stage('Publish Results') {
            steps {
                junit 'validation-results.xml'
            }
        }
    }

    post {
        failure {
            emailext(
                subject: "Conversation Validation Failed",
                body: "One or more conversation validations failed. Check Jenkins for details.",
                to: "dev-team@company.com"
            )
        }
    }
}
```

### GitLab CI

**.gitlab-ci.yml**:
```yaml
stages:
  - test
  - report

conversation_validation:
  stage: test
  image: python:3.11
  before_script:
    - pip install hapyy-conversational-qa
  script:
    - hapyy-qa validate-dir tests/conversations/ --output-format junit
  artifacts:
    reports:
      junit: validation-results.xml
    paths:
      - validation-results.xml
    when: always
  only:
    changes:
      - src/chatbot/**
      - tests/conversations/**

validation_report:
  stage: report
  dependencies:
    - conversation_validation
  script:
    - hapyy-qa report --input validation-results.xml --output report.html --format html
  artifacts:
    paths:
      - report.html
    expire_in: 30 days
```

### CircleCI

**.circleci/config.yml**:
```yaml
version: 2.1

orbs:
  python: circleci/python@2.1.1

jobs:
  validate-conversations:
    executor: python/default
    steps:
      - checkout
      - python/install-packages:
          pkg-manager: pip
          args: hapyy-conversational-qa
      - run:
          name: Validate conversations
          command: |
            hapyy-qa validate-dir tests/conversations/ \
              --output-format junit \
              --output-file test-results/validation-results.xml
      - store_test_results:
          path: test-results
      - store_artifacts:
          path: test-results/validation-results.xml

workflows:
  main:
    jobs:
      - validate-conversations:
          filters:
            branches:
              only:
                - main
                - develop
```

## IDE Extensions

### VS Code Extension

**Extension Name**: `hapyy.conversational-qa`

**Features**:
- **Inline Validation**: Validate conversation specs directly in editor
- **Autocomplete**: Suggestions for entity names, business rules, compliance checks
- **Error Highlighting**: Red squiggles for validation failures
- **Quick Fixes**: Suggested corrections for common errors
- **Test Runner**: Run validations from command palette

**Installation**:
```bash
code --install-extension hapyy.conversational-qa
```

**Configuration** (`.vscode/settings.json`):
```json
{
  "hapyy.apiKey": "${env:HAPYY_API_KEY}",
  "hapyy.knowledgeBase": {
    "clientId": "healthco",
    "version": "latest"
  },
  "hapyy.validationMode": "remote",
  "hapyy.liveValidation": true,
  "hapyy.cacheEnabled": true
}
```

**Usage**:
1. Open conversation spec file (`.yml`)
2. Extension automatically validates on save
3. Hover over highlighted errors for explanations
4. Click "Quick Fix" lightbulb for suggestions

### PyCharm Plugin

**Plugin Name**: `Hapyy Conversational QA`

**Features**:
- Integration with PyCharm's test runner
- Run/debug conversation validations
- Coverage visualization (which conversations tested)
- Performance profiling (validation latency per conversation)

**Installation**: Via JetBrains Marketplace

## Local Validation Mode

**Purpose**: Fast validation without API calls for basic checks

**Capabilities**:
- Entity extraction validation
- Schema validation (entities match expected types)
- Simple arithmetic checks
- Regex pattern matching

**Limitations**:
- No access to full knowledge base (limited to local rules)
- No SMT solver (no mathematical proofs)
- Lower accuracy than remote validation

**Configuration**:
```python
validator = HapyyValidator(validation_mode='local')
```

**Use Cases**:
- Developer laptop without internet connection
- Ultra-low latency requirements (<50ms)
- CI/CD for PR previews (fast feedback before comprehensive validation)

**Hybrid Mode**:
```python
validator = HapyyValidator(
    validation_mode='hybrid',
    local_first=True  # Try local, fallback to remote if uncertain
)
```

## Caching Strategy

### Cache Architecture

**Storage**: SQLite database (`~/.hapyy/cache.db`)

**Schema**:
```sql
CREATE TABLE validation_cache (
    cache_key TEXT PRIMARY KEY,
    conversation_hash TEXT,
    knowledge_base_version TEXT,
    validation_result TEXT,  -- JSON
    cached_at TIMESTAMP,
    ttl INTEGER
);

CREATE INDEX idx_kb_version ON validation_cache(knowledge_base_version);
CREATE INDEX idx_cached_at ON validation_cache(cached_at);
```

**Cache Key Generation**:
```python
cache_key = sha256(
    f"{user_query}|{bot_response}|{context_json}|{knowledge_base_version}"
).hexdigest()
```

**Cache Hit Conditions**:
- Exact match on conversation (query + response + context)
- Same knowledge base version
- Cache entry not expired (within TTL)

**Cache Invalidation**:
- **Time-based**: Default 24-hour TTL
- **Version-based**: Automatic invalidation when knowledge base updated
- **Manual**: `hapyy-qa cache clear` command

**Performance Impact**:
- **Cache hit**: <10ms (SQLite query)
- **Cache miss**: 300-500ms (remote validation)
- **Cache hit rate**: 60-80% in typical development workflows

### Cache Warming

**Pre-populate cache with common conversations**:
```bash
hapyy-qa cache warm \
  --specs tests/conversations/*.yml \
  --knowledge-base healthco \
  --version 2024-Q4
```

**Use Case**: Speed up CI/CD by warming cache before running tests

## Error Handling and Debugging

### Error Types

**1. API Errors**:
- **401 Unauthorized**: Invalid API key
- **403 Forbidden**: API key lacks permission for knowledge base
- **429 Too Many Requests**: Rate limit exceeded
- **500 Internal Server Error**: Validation service error

**Handling**:
```python
from hapyy_qa import HapyyValidator, HapyyAPIError

validator = HapyyValidator()

try:
    result = validator.validate(...)
except HapyyAPIError as e:
    if e.status_code == 401:
        print("ERROR: Invalid API key. Check HAPYY_API_KEY environment variable.")
    elif e.status_code == 429:
        print("ERROR: Rate limit exceeded. Retry in 60 seconds.")
    else:
        print(f"ERROR: API error {e.status_code}: {e.message}")
```

**2. Validation Errors**:
- **INVALID**: Response failed validation (business logic error)
- **UNKNOWN**: Validation inconclusive (timeout, ambiguity)

**Handling**:
```python
result = validator.validate(...)

if result.status == 'INVALID':
    print(f"Validation failed: {result.explanation}")
    print(f"Counterexample: {result.counterexample}")
    print(f"Suggestion: {result.suggestion}")
elif result.status == 'UNKNOWN':
    print(f"Validation inconclusive: {result.explanation}")
    print(f"Consider: {result.suggestion}")
```

**3. Configuration Errors**:
- Missing API key
- Invalid knowledge base ID
- Malformed conversation spec

**Handling**: Detailed error messages with configuration suggestions

### Debug Mode

**Enable verbose logging**:
```python
validator = HapyyValidator(debug=True)
```

**Output**:
```
[DEBUG] Loading conversation spec: tests/conversations/pricing_quote.yml
[DEBUG] Parsed conversation: 5 turns
[DEBUG] Entities extracted: plan=Plan A, deductible=500, premium=347
[DEBUG] Knowledge base: healthco v2024-Q4
[DEBUG] Validation request: POST https://validation.hapyy.ai/v1/validate
[DEBUG] Request latency: 287ms
[DEBUG] Cache miss: 3a7f9b2e1c...
[DEBUG] SMT solver time: 145ms
[DEBUG] Validation result: VALID (confidence 1.0)
```

**CLI Debug Mode**:
```bash
hapyy-qa validate-spec tests/conversations/pricing_quote.yml --debug
```

## Performance Optimization

### Batching

**Batch multiple validations in single API call**:
```python
results = validator.validate_batch([
    {"user_query": "...", "bot_response": "...", "context": {...}},
    {"user_query": "...", "bot_response": "...", "context": {...}},
    # ... up to 100 conversations
])
```

**Benefits**:
- Reduce HTTP overhead (1 connection instead of 100)
- Server-side parallelization
- 3-5x throughput improvement

### Parallel Validation

**Validate multiple specs in parallel**:
```python
from concurrent.futures import ThreadPoolExecutor

specs = [
    "tests/conversations/pricing_quote.yml",
    "tests/conversations/eligibility_check.yml",
    # ... 50 specs
]

with ThreadPoolExecutor(max_workers=8) as executor:
    results = list(executor.map(validator.validate_spec, specs))
```

**Performance**: 8 concurrent validations ~6x faster than sequential

### Streaming Validation

**For real-time conversational interfaces**:
```python
for result in validator.validate_stream(conversation_turns):
    if not result.is_valid:
        print(f"Turn {result.turn_index} failed: {result.explanation}")
        break
```

**Use Case**: Validate conversation turn-by-turn during live chat

## Pricing and Licensing

### SDK License

**Core SDK**: Apache 2.0 License (open source)
- Free to use, modify, distribute
- No restrictions on commercial use
- Source code on GitHub: https://github.com/hapyy/conversational-qa-sdk

### API Pricing

**Free Tier**:
- 1,000 validations/month
- Community support (GitHub issues)
- Public knowledge bases only

**Developer Tier** ($99/month):
- 10,000 validations/month
- Email support
- Custom knowledge bases (up to 3)
- Priority API (faster response times)

**Team Tier** ($499/month):
- 100,000 validations/month
- Slack support channel
- Unlimited knowledge bases
- Dedicated validation cluster (lower latency)

**Enterprise Tier** (custom pricing):
- Unlimited validations
- On-premise deployment option
- SLA guarantees (99.9% uptime)
- Dedicated customer success manager
- Custom integrations and features

## Documentation and Support

### Documentation

**Developer Portal**: https://docs.hapyy.ai

**Sections**:
- **Getting Started**: 5-minute quickstart guide
- **API Reference**: Complete API documentation (auto-generated from code)
- **Conversation Spec Guide**: DSL syntax and examples
- **Integration Guides**: pytest, Jest, JUnit, CI/CD
- **Knowledge Base Management**: Creating and updating knowledge bases
- **Best Practices**: Performance tips, testing strategies
- **Troubleshooting**: Common errors and solutions

**Examples Repository**: https://github.com/hapyy/qa-examples
- Sample conversation specs for different industries
- Reference implementations for popular chatbot frameworks
- CI/CD pipeline templates

### Support Channels

**Community Support** (free tier):
- GitHub Issues: Bug reports and feature requests
- GitHub Discussions: Q&A and community help
- Stack Overflow: Tag `hapyy-qa`

**Email Support** (paid tiers):
- Response time: <24 hours (Developer), <4 hours (Team)
- Email: support@hapyy.ai

**Slack Support** (Team and Enterprise):
- Dedicated Slack channel
- Direct access to engineering team
- Response time: <1 hour during business hours

**Customer Success** (Enterprise):
- Dedicated CSM
- Quarterly business reviews
- Custom training and onboarding

## Roadmap

### Current Version (v1.0)

- Python, Node.js, Java SDKs
- Conversation spec DSL (YAML)
- pytest, Jest, JUnit integration
- CLI tool
- Remote and local validation modes
- Caching layer
- VS Code extension

### Planned Features (v1.1 - Q2 2025)

- **Additional Languages**: Ruby, Go, C# SDKs
- **Visual Spec Editor**: Web-based conversation spec editor with live preview
- **Performance Profiling**: Identify slow validations, optimize knowledge bases
- **Regression Testing**: Automatic detection of validation changes between code versions
- **Conversation Recording**: Record live chatbot conversations and convert to test specs

### Future Features (v2.0 - Q4 2025)

- **AI-Assisted Test Generation**: Generate conversation specs from business requirements
- **Multi-Language Support**: Validate conversations in Spanish, French, German, etc.
- **Voice Conversation Validation**: Support for voice assistants (Alexa, Google Assistant)
- **Integration Marketplace**: Pre-built integrations for popular chatbot platforms (Rasa, Dialogflow, Botpress)
- **Collaborative Knowledge Bases**: Multiple team members editing knowledge bases simultaneously

## References

1. **Test-Driven Development**:
   - Beck, K. (2002). "Test-Driven Development: By Example". Addison-Wesley.
   - Martin, R. C. (2008). "Clean Code: A Handbook of Agile Software Craftsmanship". Prentice Hall.

2. **SDK Design Principles**:
   - Bloch, J. (2018). "Effective Java, 3rd Edition". Addison-Wesley.
   - "API Design Best Practices". Google Cloud Documentation.

3. **Conversational AI Testing**:
   - Rasa, "Conversation Testing Guide". https://rasa.com/docs/rasa/testing-your-assistant
   - Bocklisch, T., et al. (2017). "Rasa: Open Source Language Understanding and Dialogue Management". NIPS Conversational AI Workshop.

4. **CI/CD Integration**:
   - Humble, J., & Farley, D. (2010). "Continuous Delivery". Addison-Wesley.
   - "GitHub Actions Documentation". https://docs.github.com/en/actions

5. **Developer Experience**:
   - Winters, T., et al. (2020). "Software Engineering at Google". O'Reilly Media.
   - "Developer Experience: Concept and Definition". IEEE Software, 2019.

6. **Testing Frameworks**:
   - "pytest Documentation". https://docs.pytest.org/
   - "Jest Documentation". https://jestjs.io/docs/getting-started
   - "JUnit 5 User Guide". https://junit.org/junit5/docs/current/user-guide/

7. **Caching Strategies**:
   - "Caching Best Practices". AWS Documentation.
   - Kleppmann, M. (2017). "Designing Data-Intensive Applications". O'Reilly Media.