# Knowledge Base Management Architecture

**Research Date**: January 2025
**Sprint**: 02 - Conversational AI Quality Assurance
**Task**: 03 - Solution Architecture Design
**Researcher**: Solution Architect Skill

## Executive Summary

The Knowledge Base Management system is the source of truth for all conversational AI validation, encoding business rules, pricing formulas, policies, regulatory requirements, and domain knowledge into machine-readable SMT constraints. This component transforms implicit business logic (scattered across spreadsheets, policy documents, legacy systems, and tribal knowledge) into explicit, versioned, validated truth sources that enable deterministic validation of chatbot responses. The business value is substantial: eliminate inconsistencies between documentation and implementation, provide audit trails for regulatory compliance, enable business users to update rules without engineering intervention, and ensure chatbot responses reflect the current, correct business logic at all times.

For Innova's AIDI platform specifically, this means each client (healthcare, insurance, financial services) maintains their own isolated knowledge base containing pricing tables, eligibility criteria, coverage limits, regulatory rules, and product catalogs. Business analysts can update pricing (quarterly) or policies (ad-hoc) through a web interface, with changes automatically converted to SMT constraints, validated for internal consistency, version-controlled with Git, and deployed to production with rollback capability. This empowers business teams while maintaining technical rigor and compliance.

The architecture emphasizes multi-tenancy (strict data isolation per client), version control (full audit trail of all changes), conflict detection (identify contradictory rules before deployment), schema flexibility (support diverse business domains), and integration adaptability (connect to existing databases, APIs, files as truth sources).

## Key Design Decisions

- **Git-Based Version Control**: All knowledge bases stored in Git repositories for complete change history, branching, rollback, and audit compliance
- **Multi-Tenant Architecture**: Strict data isolation per client with separate Git repositories, ensuring security and preventing cross-contamination
- **Schema-First Design**: Define business rule schemas in JSON Schema or Protobuf, enabling validation and IDE autocomplete for rule authors
- **Declarative Rule Format**: YAML for human readability, compiled to SMT constraints for solver consumption
- **Truth Source Federation**: Pluggable adapters for databases (PostgreSQL, MySQL), APIs (REST, GraphQL), files (CSV, JSON, Excel), enabling reuse of existing data
- **Rule Conflict Detection**: Automated validation of rule consistency using SMT solver before deployment (e.g., detect if two pricing rules contradict)
- **Staged Deployment**: Dev → Staging → Production workflow with approval gates and automated testing
- **Web-Based Editor**: Self-service interface for business users to update rules without coding, with validation and preview
- **API-First Access**: RESTful API for programmatic rule management, enabling CI/CD integration

## Knowledge Base Architecture

### Component Overview

**Textual Architecture Diagram**:

```
┌─────────────────────────────────────────────────────────────────┐
│                    BUSINESS USERS & SYSTEMS                      │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │  Web Editor  │  │  Excel       │  │  External Systems    │  │
│  │  (Browser)   │  │  Import      │  │  (CRM, ERP, DB)      │  │
│  └──────┬───────┘  └──────┬───────┘  └──────────┬───────────┘  │
└─────────┼──────────────────┼─────────────────────┼──────────────┘
          │                  │                     │
          │ HTTPS            │ File Upload         │ REST API
          │                  │                     │
┌─────────▼──────────────────▼─────────────────────▼──────────────┐
│                   KNOWLEDGE BASE API LAYER                       │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ REST API (FastAPI)                                       │  │
│  │  - POST /kb/{client_id}/rules (Create/Update)           │  │
│  │  - GET /kb/{client_id}/rules (List)                     │  │
│  │  - GET /kb/{client_id}/rules/{rule_id} (Retrieve)       │  │
│  │  - DELETE /kb/{client_id}/rules/{rule_id}               │  │
│  │  - POST /kb/{client_id}/validate (Test rules)           │  │
│  │  - POST /kb/{client_id}/deploy (Deploy to production)   │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│                      RULE PROCESSING LAYER                       │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Schema Validator                                         │  │
│  │  - Validate YAML against JSON Schema                     │  │
│  │  - Check required fields, data types                     │  │
│  └────────────────────────────┬─────────────────────────────┘  │
│  ┌────────────────────────────▼─────────────────────────────┐  │
│  │ Rule Compiler                                            │  │
│  │  - YAML business rules → SMT-LIB constraints             │  │
│  │  - Optimize formulas (simplification)                    │  │
│  └────────────────────────────┬─────────────────────────────┘  │
│  ┌────────────────────────────▼─────────────────────────────┐  │
│  │ Conflict Detector                                        │  │
│  │  - Check rule consistency using SMT solver               │  │
│  │  - Identify contradictions (e.g., A=5 AND A=10)          │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│                   VERSION CONTROL LAYER (Git)                    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Git Repository (per client)                              │  │
│  │  repos/healthco/                                         │  │
│  │    ├── pricing_rules.yml                                 │  │
│  │    ├── eligibility_rules.yml                             │  │
│  │    ├── coverage_limits.yml                               │  │
│  │    ├── schemas/pricing_schema.json                       │  │
│  │    └── .git/ (version history)                           │  │
│  └────────────────────────────┬─────────────────────────────┘  │
│  ┌────────────────────────────▼─────────────────────────────┐  │
│  │ Version Manager                                          │  │
│  │  - Git commit on every rule change                       │  │
│  │  - Semantic versioning (v2024-Q4, v2025-Q1)              │  │
│  │  - Branch management (dev, staging, production)          │  │
│  │  - Rollback capability (git revert)                      │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│                    TRUTH SOURCE CONNECTORS                       │
│  ┌──────────────────┐  ┌─────────────────┐  ┌──────────────┐  │
│  │  Database        │  │  REST API       │  │  File        │  │
│  │  Connector       │  │  Connector      │  │  Connector   │  │
│  │  (PostgreSQL,    │  │  (External      │  │  (CSV, JSON, │  │
│  │   MySQL, etc.)   │  │   Services)     │  │   Excel)     │  │
│  └────────┬─────────┘  └────────┬────────┘  └──────┬───────┘  │
└───────────┼─────────────────────┼────────────────────┼──────────┘
            │                     │                    │
┌───────────▼─────────────────────▼────────────────────▼──────────┐
│                  EXTERNAL TRUTH SOURCES                          │
│  ┌──────────────┐  ┌───────────────┐  ┌─────────────────────┐  │
│  │  Client DB   │  │  Pricing API  │  │  Policy Documents   │  │
│  │  (CRM data)  │  │  (Rating Eng) │  │  (PDF, DOCX)        │  │
│  └──────────────┘  └───────────────┘  └─────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

### Knowledge Base Schema

**Purpose**: Define structure of business rules for validation and IDE support

**Example Schema** (JSON Schema for insurance pricing rules):
```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "Insurance Pricing Rules Schema",
  "type": "object",
  "required": ["plan_id", "pricing_formula", "deductible_options"],
  "properties": {
    "plan_id": {
      "type": "string",
      "pattern": "^plan_[a-z0-9_]+$",
      "description": "Unique plan identifier"
    },
    "plan_name": {
      "type": "string",
      "description": "Human-readable plan name"
    },
    "pricing_formula": {
      "type": "object",
      "required": ["base_rate", "age_factors"],
      "properties": {
        "base_rate": {
          "type": "number",
          "minimum": 0,
          "description": "Base monthly premium in USD"
        },
        "age_factors": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["min_age", "max_age", "factor"],
            "properties": {
              "min_age": {"type": "integer", "minimum": 18, "maximum": 100},
              "max_age": {"type": "integer", "minimum": 18, "maximum": 100},
              "factor": {"type": "number", "minimum": 0}
            }
          }
        },
        "deductible_discounts": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["deductible", "discount"],
            "properties": {
              "deductible": {"type": "integer", "enum": [500, 1000, 2500, 5000]},
              "discount": {"type": "number"}
            }
          }
        }
      }
    },
    "deductible_options": {
      "type": "array",
      "items": {"type": "integer"},
      "minItems": 1,
      "uniqueItems": true
    },
    "eligibility_rules": {
      "type": "object",
      "properties": {
        "min_age": {"type": "integer", "minimum": 0},
        "max_age": {"type": "integer", "maximum": 120},
        "excluded_conditions": {
          "type": "array",
          "items": {"type": "string"}
        }
      }
    }
  }
}
```

**Example Business Rule** (YAML conforming to schema):
```yaml
plan_id: plan_a
plan_name: "Plan A - Bronze"
pricing_formula:
  base_rate: 285
  age_factors:
    - min_age: 18
      max_age: 25
      factor: 0
    - min_age: 26
      max_age: 35
      factor: 25
    - min_age: 36
      max_age: 45
      factor: 62
    - min_age: 46
      max_age: 55
      factor: 120
    - min_age: 56
      max_age: 65
      factor: 180
  deductible_discounts:
    - deductible: 500
      discount: 0
    - deductible: 1000
      discount: -15
    - deductible: 2500
      discount: -35
    - deductible: 5000
      discount: -60
deductible_options: [500, 1000, 2500, 5000]
eligibility_rules:
  min_age: 18
  max_age: 65
  excluded_conditions:
    - active_cancer
    - end_stage_renal_disease
```

### Rule Compilation

**Purpose**: Convert YAML business rules to SMT-LIB constraints

**Compiler Architecture**:
```python
class RuleCompiler:
    def __init__(self, schema):
        self.schema = schema

    def compile_pricing_rule(self, rule_yaml):
        """Compile pricing rule YAML to SMT-LIB formula"""
        # Parse YAML
        rule = yaml.safe_load(rule_yaml)

        # Validate against schema
        jsonschema.validate(rule, self.schema)

        # Generate SMT formula
        formula_parts = []

        # Declare constants
        formula_parts.append("(declare-const plan String)")
        formula_parts.append("(declare-const age Int)")
        formula_parts.append("(declare-const deductible Int)")
        formula_parts.append("(declare-const premium Int)")

        # Plan constraint
        formula_parts.append(f"(assert (= plan \"{rule['plan_id']}\"))")

        # Age factor lookup function
        age_factors = rule['pricing_formula']['age_factors']
        age_factor_cases = []
        for af in age_factors:
            age_factor_cases.append(
                f"(ite (and (>= age {af['min_age']}) (<= age {af['max_age']})) {af['factor']})"
            )

        # Deductible discount lookup
        deductible_discounts = rule['pricing_formula']['deductible_discounts']
        deductible_discount_cases = []
        for dd in deductible_discounts:
            deductible_discount_cases.append(
                f"(ite (= deductible {dd['deductible']}) {dd['discount']})"
            )

        # Pricing formula: premium = base_rate + age_factor + deductible_discount
        base_rate = rule['pricing_formula']['base_rate']
        formula_parts.append(
            f"(assert (= premium (+ {base_rate} "
            f"{' '.join(age_factor_cases)} "
            f"{' '.join(deductible_discount_cases)})))"
        )

        # Deductible options constraint
        deductible_options = rule['deductible_options']
        deductible_constraint = f"(or {' '.join([f'(= deductible {d})' for d in deductible_options])})"
        formula_parts.append(f"(assert {deductible_constraint})")

        # Eligibility constraints
        if 'eligibility_rules' in rule:
            min_age = rule['eligibility_rules']['min_age']
            max_age = rule['eligibility_rules']['max_age']
            formula_parts.append(f"(assert (and (>= age {min_age}) (<= age {max_age})))")

        # Combine formula parts
        formula = "\n".join(formula_parts)

        return formula
```

**Usage**:
```python
compiler = RuleCompiler(pricing_schema)

# Compile rule
rule_yaml = open('pricing_rules.yml').read()
smt_formula = compiler.compile_pricing_rule(rule_yaml)

print(smt_formula)
```

**Output**:
```smt-lib
(declare-const plan String)
(declare-const age Int)
(declare-const deductible Int)
(declare-const premium Int)
(assert (= plan "plan_a"))
(assert (= premium (+ 285
  (ite (and (>= age 18) (<= age 25)) 0)
  (ite (and (>= age 26) (<= age 35)) 25)
  (ite (and (>= age 36) (<= age 45)) 62)
  (ite (and (>= age 46) (<= age 55)) 120)
  (ite (and (>= age 56) (<= age 65)) 180)
  (ite (= deductible 500) 0)
  (ite (= deductible 1000) -15)
  (ite (= deductible 2500) -35)
  (ite (= deductible 5000) -60))))
(assert (or (= deductible 500) (= deductible 1000) (= deductible 2500) (= deductible 5000)))
(assert (and (>= age 18) (<= age 65)))
```

### Conflict Detection

**Purpose**: Validate that business rules are internally consistent before deployment

**Strategy**: Use SMT solver to check if rules are satisfiable

**Example Conflict**:
```yaml
# Rule 1: Premium for Plan A, age 45, deductible 500 is $347
pricing_rules:
  - plan: plan_a
    age: 45
    deductible: 500
    premium: 347

# Rule 2: Premium for Plan A, age 45, deductible 500 is $350 (CONFLICT!)
pricing_rules:
  - plan: plan_a
    age: 45
    deductible: 500
    premium: 350
```

**Conflict Detection Algorithm**:
```python
def detect_conflicts(rules):
    """Detect conflicting rules using SMT solver"""
    solver = Solver()

    # Add all rules as constraints
    for rule in rules:
        formula = compile_rule(rule)
        solver.from_string(formula)

    # Check satisfiability
    result = solver.check()

    if result == unsat:
        # Rules are contradictory
        core = solver.unsat_core()
        return {
            'has_conflict': True,
            'conflicting_rules': extract_conflicting_rules(core)
        }
    elif result == sat:
        # Rules are consistent
        return {'has_conflict': False}
    else:
        # Unknown (timeout or complex)
        return {'has_conflict': 'unknown'}
```

**Conflict Report**:
```json
{
  "has_conflict": true,
  "conflicting_rules": [
    {
      "rule_id": "pricing_plan_a_age45_ded500_v1",
      "premium": 347
    },
    {
      "rule_id": "pricing_plan_a_age45_ded500_v2",
      "premium": 350
    }
  ],
  "explanation": "Premium for Plan A, age 45, deductible $500 cannot be both $347 and $350.",
  "suggestion": "Review pricing rules and ensure only one premium value for each plan/age/deductible combination."
}
```

### Version Control

**Git Repository Structure** (per client):
```
repos/healthco/
  ├── .git/                      # Git version history
  ├── README.md                  # Client-specific documentation
  ├── schemas/                   # JSON schemas
  │   ├── pricing_schema.json
  │   ├── eligibility_schema.json
  │   └── coverage_schema.json
  ├── rules/                     # Business rules (YAML)
  │   ├── pricing/
  │   │   ├── plan_a.yml
  │   │   ├── plan_b.yml
  │   │   └── plan_c.yml
  │   ├── eligibility/
  │   │   ├── age_limits.yml
  │   │   └── excluded_conditions.yml
  │   └── coverage/
  │       ├── annual_limits.yml
  │       └── copays.yml
  ├── compiled/                  # Compiled SMT formulas (auto-generated)
  │   ├── pricing_plan_a.smt2
  │   ├── pricing_plan_b.smt2
  │   └── eligibility.smt2
  └── tests/                     # Validation tests
      ├── test_pricing.yml
      └── test_eligibility.yml
```

**Semantic Versioning**:
- Format: `v{YEAR}-Q{QUARTER}` (e.g., `v2024-Q4`, `v2025-Q1`)
- Git tags for releases
- Git branches: `dev`, `staging`, `production`

**Change Workflow**:
1. **Edit Rules**: Business analyst updates pricing_rules.yml in `dev` branch
2. **Validate**: Automated validation (schema check, conflict detection)
3. **Commit**: Git commit with message (e.g., "Update Plan A pricing for 2025")
4. **Test**: Run validation tests against test conversations
5. **Merge to Staging**: Deploy to staging environment, validate with real conversations
6. **Approve**: Business owner approves deployment
7. **Merge to Production**: Deploy to production, tag with version (e.g., `v2025-Q1`)
8. **Rollback**: If issues, revert commit and redeploy previous version

**Audit Trail**:
```bash
git log --oneline
```

**Output**:
```
a3f9b2e (HEAD -> production, tag: v2025-Q1) Update Plan A pricing for 2025
7c1d8e4 (tag: v2024-Q4) Add Plan D coverage limits
5b2a9f1 Fix eligibility age range for Plan C
3e8c7a2 Initial knowledge base setup
```

### Truth Source Connectors

**Purpose**: Fetch business rules from external systems (databases, APIs, files)

**Database Connector** (PostgreSQL example):
```python
import psycopg2
import yaml

class DatabaseConnector:
    def __init__(self, connection_string):
        self.conn = psycopg2.connect(connection_string)

    def fetch_pricing_rules(self, plan_id):
        """Fetch pricing rules from database"""
        cursor = self.conn.cursor()

        # Query pricing table
        cursor.execute("""
            SELECT base_rate, age_min, age_max, age_factor,
                   deductible, deductible_discount
            FROM pricing_rules
            WHERE plan_id = %s
        """, (plan_id,))

        rows = cursor.fetchall()

        # Convert to YAML format
        rule = {
            'plan_id': plan_id,
            'pricing_formula': {
                'base_rate': rows[0][0],
                'age_factors': [],
                'deductible_discounts': []
            }
        }

        for row in rows:
            rule['pricing_formula']['age_factors'].append({
                'min_age': row[1],
                'max_age': row[2],
                'factor': row[3]
            })
            rule['pricing_formula']['deductible_discounts'].append({
                'deductible': row[4],
                'discount': row[5]
            })

        return yaml.dump(rule)
```

**REST API Connector**:
```python
import requests

class APIConnector:
    def __init__(self, base_url, api_key):
        self.base_url = base_url
        self.api_key = api_key

    def fetch_pricing_rules(self, plan_id):
        """Fetch pricing rules from external API"""
        response = requests.get(
            f"{self.base_url}/plans/{plan_id}/pricing",
            headers={'Authorization': f'Bearer {self.api_key}'}
        )

        data = response.json()

        # Convert API response to YAML format
        rule = {
            'plan_id': data['id'],
            'pricing_formula': data['pricing']
        }

        return yaml.dump(rule)
```

**File Connector** (Excel example):
```python
import pandas as pd

class ExcelConnector:
    def __init__(self, file_path):
        self.file_path = file_path

    def fetch_pricing_rules(self):
        """Fetch pricing rules from Excel spreadsheet"""
        df = pd.read_excel(self.file_path, sheet_name='Pricing')

        rules = []
        for plan_id in df['plan_id'].unique():
            plan_data = df[df['plan_id'] == plan_id]

            rule = {
                'plan_id': plan_id,
                'pricing_formula': {
                    'base_rate': plan_data.iloc[0]['base_rate'],
                    'age_factors': plan_data[['min_age', 'max_age', 'age_factor']].to_dict('records'),
                    'deductible_discounts': plan_data[['deductible', 'discount']].to_dict('records')
                }
            }

            rules.append(rule)

        return yaml.dump(rules)
```

**Sync Strategy**:
- **Manual Sync**: Business analyst triggers sync via web interface
- **Scheduled Sync**: Nightly sync from external systems (cron job)
- **Event-Driven Sync**: Webhook triggers sync on external system update

### Web-Based Editor

**Purpose**: Enable business users to update rules without coding

**Features**:
- **WYSIWYG Editor**: Edit YAML with syntax highlighting and validation
- **Form-Based Editor**: Fill out forms instead of editing raw YAML
- **Preview**: Preview how changes will affect validation results
- **Diff View**: See what changed compared to previous version
- **Approval Workflow**: Submit changes for review before deployment

**Technology Stack**:
- **Frontend**: React + Monaco Editor (VS Code's editor)
- **Backend**: FastAPI REST API
- **Authentication**: OAuth 2.0 (Auth0 or AWS Cognito)
- **Authorization**: Role-based access control (Admin, Editor, Viewer)

**UI Mockup** (textual):
```
┌─────────────────────────────────────────────────────────────────┐
│  Hapyy Knowledge Base Editor                    [HealthCo]      │
├─────────────────────────────────────────────────────────────────┤
│  [Pricing Rules] [Eligibility Rules] [Coverage Limits]          │
├─────────────────────────────────────────────────────────────────┤
│  Plan A - Bronze                                   [Edit] [Save] │
│                                                                  │
│  Base Rate: [285] USD/month                                     │
│                                                                  │
│  Age Factors:                                                   │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │ Age Range      │ Factor                    [+ Add Row]     │ │
│  ├────────────────┼──────────────────────────────────────────┤ │
│  │ 18 - 25        │ 0                                        │ │
│  │ 26 - 35        │ 25                                       │ │
│  │ 36 - 45        │ 62                                       │ │
│  │ 46 - 55        │ 120                                      │ │
│  │ 56 - 65        │ 180                                      │ │
│  └────────────────┴──────────────────────────────────────────┘ │
│                                                                  │
│  Deductible Discounts:                                          │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │ Deductible     │ Discount                  [+ Add Row]     │ │
│  ├────────────────┼──────────────────────────────────────────┤ │
│  │ $500           │ $0                                       │ │
│  │ $1,000         │ -$15                                     │ │
│  │ $2,500         │ -$35                                     │ │
│  │ $5,000         │ -$60                                     │ │
│  └────────────────┴──────────────────────────────────────────┘ │
│                                                                  │
│  [Preview Changes]  [Submit for Approval]  [Cancel]             │
└─────────────────────────────────────────────────────────────────┘
```

**Validation**:
- Real-time schema validation as user types
- Conflict detection before save
- Preview validation results against test conversations

### API Endpoints

**REST API** (FastAPI):

**List Knowledge Bases**:
```
GET /api/v1/kb
Response: [
  {"client_id": "healthco", "name": "HealthCo Insurance", "version": "v2024-Q4"},
  {"client_id": "autoinsure", "name": "AutoInsure Inc", "version": "v2024-Q3"}
]
```

**Get Rules**:
```
GET /api/v1/kb/{client_id}/rules/pricing
Response: {
  "plan_a": {...},
  "plan_b": {...}
}
```

**Create/Update Rule**:
```
POST /api/v1/kb/{client_id}/rules/pricing/plan_a
Body: {
  "plan_id": "plan_a",
  "pricing_formula": {...}
}
Response: {
  "status": "success",
  "rule_id": "pricing_plan_a",
  "version": "v2025-Q1"
}
```

**Delete Rule**:
```
DELETE /api/v1/kb/{client_id}/rules/pricing/plan_a
Response: {"status": "deleted"}
```

**Validate Rules**:
```
POST /api/v1/kb/{client_id}/validate
Body: {
  "rules": [...],
  "test_conversations": [...]
}
Response: {
  "valid": true,
  "conflicts": [],
  "test_results": [...]
}
```

**Deploy to Production**:
```
POST /api/v1/kb/{client_id}/deploy
Body: {
  "version": "v2025-Q1",
  "environment": "production"
}
Response: {
  "status": "deployed",
  "git_tag": "v2025-Q1",
  "deployed_at": "2025-01-15T14:30:00Z"
}
```

### Multi-Tenancy & Security

**Data Isolation**:
- Each client has separate Git repository
- PostgreSQL row-level security (RLS) for database-backed rules
- API authentication includes client_id scope

**Access Control**:
- **Admin**: Full access to all clients
- **Client Admin**: Full access to specific client's knowledge base
- **Editor**: Edit rules, submit for approval
- **Viewer**: Read-only access

**API Authentication**:
```
Authorization: Bearer <jwt_token>
```

**JWT Token Payload**:
```json
{
  "sub": "user_123",
  "email": "analyst@healthco.com",
  "client_id": "healthco",
  "role": "editor",
  "exp": 1672531200
}
```

### Staging and Deployment

**Environments**:
- **Development**: Experimental rules, frequent changes
- **Staging**: Pre-production testing with real conversations
- **Production**: Live validation

**Deployment Workflow**:
1. **Create Feature Branch**: `git checkout -b feature/update-plan-a-pricing`
2. **Edit Rules**: Update pricing_rules.yml
3. **Validate**: Run automated tests
4. **Merge to Dev**: `git merge dev`
5. **Deploy to Dev**: Automated deployment on merge
6. **Merge to Staging**: Create PR, require approval
7. **Deploy to Staging**: Automated deployment, run smoke tests
8. **Merge to Production**: Create PR, require business owner approval
9. **Deploy to Production**: Automated deployment, tag release

**Automated Testing**:
```yaml
# .github/workflows/validate-kb.yml
name: Validate Knowledge Base

on:
  pull_request:
    branches: [staging, production]

jobs:
  validate:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Validate Schema
        run: |
          jsonschema -i rules/pricing/plan_a.yml schemas/pricing_schema.json
      - name: Detect Conflicts
        run: |
          python scripts/detect_conflicts.py
      - name: Run Validation Tests
        run: |
          hapyy-qa validate-dir tests/
```

### Rollback Capability

**Rollback Process**:
1. Identify issue with current production version
2. Identify last known good version (Git tag)
3. Revert to previous version: `git revert <commit>`
4. Deploy: Automated deployment of reverted version
5. Verify: Run smoke tests

**Example**:
```bash
# Current production: v2025-Q1 (has issues)
# Rollback to v2024-Q4

git checkout production
git revert HEAD  # Revert latest commit
git tag v2025-Q1-rollback
git push origin production --tags

# Automated deployment triggers, restoring v2024-Q4 rules
```

**Recovery Time**: <10 minutes (automated)

### Knowledge Base Metrics

**Track**:
- Number of rules per client
- Rule complexity (lines of YAML, number of constraints)
- Update frequency (commits per month)
- Conflict detection rate (% of updates with conflicts)
- Deployment frequency (deployments per quarter)

**Alerting**:
- Alert if conflict detection finds issues before deployment
- Alert if deployment fails validation tests
- Alert if validation success rate drops after deployment

## Example: Insurance Pricing Knowledge Base

**Complete Example** (HealthCo Insurance Plan A):

**File**: `repos/healthco/rules/pricing/plan_a.yml`
```yaml
# Plan A - Bronze Level Health Insurance
# Version: v2025-Q1
# Effective Date: 2025-01-01
# Maintainer: Jane Smith (jane@healthco.com)

plan_id: plan_a
plan_name: "Plan A - Bronze"
plan_type: individual
metal_tier: bronze
aca_compliant: true

pricing_formula:
  base_rate: 285  # Monthly premium base (USD)

  age_factors:
    - min_age: 18
      max_age: 25
      factor: 0
      description: "Young adult discount"
    - min_age: 26
      max_age: 35
      factor: 25
      description: "Young professional"
    - min_age: 36
      max_age: 45
      factor: 62
      description: "Middle age"
    - min_age: 46
      max_age: 55
      factor: 120
      description: "Older adult"
    - min_age: 56
      max_age: 65
      factor: 180
      description: "Pre-Medicare"

  deductible_discounts:
    - deductible: 500
      discount: 0
      description: "Low deductible"
    - deductible: 1000
      discount: -15
      description: "Medium deductible"
    - deductible: 2500
      discount: -35
      description: "High deductible"
    - deductible: 5000
      discount: -60
      description: "Very high deductible"

  state_multipliers:
    CA: 1.15  # California: 15% higher
    NY: 1.25  # New York: 25% higher
    TX: 0.95  # Texas: 5% lower
    FL: 1.05  # Florida: 5% higher
    default: 1.00

deductible_options: [500, 1000, 2500, 5000]

eligibility_rules:
  min_age: 18
  max_age: 65
  residency_required: true
  allowed_states: [CA, NY, TX, FL]
  excluded_conditions:
    - active_cancer
    - end_stage_renal_disease
    - hospice_care

coverage_details:
  annual_max: 1000000
  out_of_pocket_max: 8000
  copay_primary_care: 30
  copay_specialist: 60
  copay_er: 500
  prescription_coverage: true

effective_date: "2025-01-01"
expiration_date: "2025-12-31"
```

**Compiled SMT Formula** (simplified):
```smt-lib
(declare-const plan String)
(declare-const age Int)
(declare-const deductible Int)
(declare-const state String)
(declare-const premium Int)

(assert (= plan "plan_a"))
(assert (and (>= age 18) (<= age 65)))
(assert (member deductible (500 1000 2500 5000)))

; Premium = base_rate * state_multiplier + age_factor + deductible_discount
(assert (= premium
  (* (ite (= state "CA") 1.15
      (ite (= state "NY") 1.25
      (ite (= state "TX") 0.95
      (ite (= state "FL") 1.05 1.00))))
     (+ 285
        (ite (and (>= age 18) (<= age 25)) 0
        (ite (and (>= age 26) (<= age 35)) 25
        (ite (and (>= age 36) (<= age 45)) 62
        (ite (and (>= age 46) (<= age 55)) 120
        (ite (and (>= age 56) (<= age 65)) 180 0)))))
        (ite (= deductible 500) 0
        (ite (= deductible 1000) -15
        (ite (= deductible 2500) -35
        (ite (= deductible 5000) -60 0))))))))

(check-sat)
(get-model)
```

## References

1. **Knowledge Representation**:
   - Russell, S., & Norvig, P. (2020). "Artificial Intelligence: A Modern Approach, 4th Edition". Pearson.
   - "JSON Schema Specification". https://json-schema.org/

2. **Version Control**:
   - Chacon, S., & Straub, B. (2014). "Pro Git, 2nd Edition". Apress.
   - "Git Documentation". https://git-scm.com/doc

3. **Business Rules Management**:
   - "Business Rules Manifesto". Business Rules Group.
   - "RETE Algorithm for Rule Engines". Forgy, C. (1982).

4. **Multi-Tenancy**:
   - Chong, F., et al. (2006). "Multi-Tenant Data Architecture". Microsoft Architecture Journal.
   - "PostgreSQL Row-Level Security". https://www.postgresql.org/docs/current/ddl-rowsecurity.html

5. **API Design**:
   - "OpenAPI Specification 3.1". https://spec.openapis.org/oas/v3.1.0
   - "REST API Best Practices". Microsoft Azure Documentation.

6. **Schema Validation**:
   - "JSON Schema Validation". https://json-schema.org/draft/2020-12/json-schema-validation.html
   - "YAML Specification". https://yaml.org/spec/