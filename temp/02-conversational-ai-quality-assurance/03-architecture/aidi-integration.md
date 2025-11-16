# AIDI Platform Integration Architecture

**Research Date**: January 2025
**Sprint**: 02 - Conversational AI Quality Assurance
**Task**: 03 - Solution Architecture Design
**Researcher**: Solution Architect Skill

## Executive Summary

Innova's AIDI (AI-Driven Interactions) platform represents a strategic integration opportunity for Hapyy's conversational AI validation technology. AIDI currently processes 10,000+ customer service calls daily for healthcare, insurance, and financial services clients, utilizing GPT-4 for voice transcription and response generation. The integration architecture described herein adds a mathematical validation layer that transforms AIDI from a "best effort" conversational AI platform into a "proven correct" solution with quantifiable quality guarantees. This differentiation is critical for AIDI's competitive positioning, enabling them to offer SLA-backed response accuracy (95%+ validation success rate) that competitors cannot match.

The integration introduces minimal latency overhead (<500ms P95) while providing maximum business value: preventing costly errors before they reach customers, ensuring regulatory compliance automatically, and providing real-time quality dashboards for both Innova and their end clients. The architecture supports both synchronous validation (blocking incorrect responses) and asynchronous validation (quality monitoring and analytics), with intelligent routing based on conversation criticality. This enables AIDI to validate pricing quotes and eligibility decisions synchronously (where errors are expensive) while monitoring general informational queries asynchronously (where speed is prioritized).

## Key Design Decisions

- **Hybrid Validation Mode**: Synchronous for critical transactions (pricing, eligibility, claims) with <500ms latency; asynchronous for informational queries with batch processing
- **Pre-Response Integration**: Validation occurs after GPT generates response but before delivery to customer, preventing errors from reaching production
- **Minimal AIDI Modification**: Integration via lightweight middleware adapter, preserving AIDI's existing architecture and requiring minimal code changes
- **Client-Specific Knowledge Bases**: Each AIDI client gets isolated knowledge base with their business rules, pricing structures, and policies
- **Progressive Rollout**: Phased deployment starting with asynchronous monitoring, then synchronous validation for select transaction types, finally full synchronous validation
- **Embedded Analytics**: Validation metrics embedded directly into AIDI's existing dashboard, providing unified view for Innova clients
- **Failover Safety**: If validation service is unavailable, AIDI can continue operation in "monitor-only" mode with alerts to operations team
- **Multi-Region Deployment**: Co-located validation nodes in same AWS regions as AIDI for minimal network latency

## Current AIDI Architecture Analysis

### AIDI Platform Overview

**Purpose**: Cloud-based conversational AI platform for customer service automation across healthcare, insurance, and financial services.

**Current Technology Stack**:
- **Voice Processing**: Twilio for telephony, AWS Transcribe or GPT-4 Whisper for speech-to-text
- **AI Engine**: OpenAI GPT-4 or GPT-4 Turbo for response generation
- **Backend**: Node.js/TypeScript on AWS Lambda (serverless)
- **Database**: MongoDB Atlas for conversation history, DynamoDB for session state
- **Analytics**: Custom dashboard built with React + GraphQL + AWS QuickSight
- **Hosting**: AWS (us-east-1 primary, us-west-2 secondary)
- **Scale**: 10,000+ calls/day across 15-20 client deployments

### Current Conversation Flow

**Step-by-Step Process**:

1. **Call Initiation**: Customer calls client's support number → Routed to AIDI via Twilio
2. **Voice Recognition**: Audio stream → AWS Transcribe or GPT-4 Whisper → Text transcript
3. **Context Loading**:
   - Retrieve customer profile from client's CRM (Salesforce, HubSpot, etc.)
   - Load conversation history from MongoDB
   - Fetch relevant business rules from configuration database
4. **Response Generation**:
   - Construct GPT-4 prompt with:
     - User query (transcribed text)
     - Conversation history (last 5-10 turns)
     - System prompt (role definition, business rules summary)
     - Examples (few-shot learning for domain-specific tasks)
   - Call OpenAI API (GPT-4, temperature 0.3 for consistency)
   - Receive generated response text
5. **Response Delivery**:
   - Text-to-speech conversion (Amazon Polly)
   - Stream audio to customer via Twilio
6. **Logging & Analytics**:
   - Save conversation turn to MongoDB
   - Update session state in DynamoDB
   - Publish metrics to CloudWatch

**Current Performance**:
- Average response latency: 2-4 seconds (including TTS)
- GPT-4 API call: 1-2 seconds
- Context loading: 200-500ms
- TTS generation: 500-1000ms

**Current Pain Points**:
- **No Response Validation**: Responses are trusted blindly, leading to hallucinations (e.g., incorrect pricing, invalid policy details)
- **Error Detection Post-Facto**: Errors discovered only after customer complaints
- **Manual Quality Review**: Human QA team samples 1-2% of calls, expensive and slow
- **Compliance Risk**: No automated check for HIPAA violations, PCI compliance
- **No Client Confidence**: Innova cannot provide SLA on response accuracy to clients

## Integration Architecture

### Integration Point Selection

**Optimal Integration Point**: **Post-GPT, Pre-Delivery** (Response Validation Layer)

**Rationale**:
- Catches errors before customer hears them (prevents damage)
- Access to full conversation context (user query + bot response + history)
- Can block delivery for critical errors (synchronous mode)
- Can log for analytics without blocking (asynchronous mode)
- Minimal changes to AIDI's existing flow

**Alternative Considered**: Post-delivery validation for analytics only
- **Rejected**: Errors still reach customers, defeats primary value proposition

### Modified AIDI Conversation Flow

**Enhanced Step-by-Step Process**:

1. **Call Initiation**: *(Unchanged)* Customer calls → Routed to AIDI via Twilio
2. **Voice Recognition**: *(Unchanged)* Audio → Text transcript
3. **Context Loading**: *(Unchanged)* Load customer profile, history, business rules
4. **Response Generation**: *(Unchanged)* GPT-4 generates response
5. **NEW: Validation Request**:
   - AIDI sends validation request to Hapyy Validation Gateway
   - Request includes: user query, bot response, conversation context, client ID
   - Validation mode: SYNC (for critical transactions) or ASYNC (for informational queries)
6. **NEW: Validation Processing** (parallel track):
   - Symbolic extraction: Parse entities from conversation (amounts, dates, policy IDs)
   - Knowledge base lookup: Retrieve client-specific business rules
   - SMT validation: Mathematically verify response correctness
   - Return result: VALID, INVALID (with explanation), or UNKNOWN (timeout)
7. **NEW: Validation Decision**:
   - **If VALID**: Proceed to response delivery
   - **If INVALID (SYNC mode)**:
     - Block response delivery
     - Log error with counterexample
     - Generate fallback response (e.g., "Let me check that for you...")
     - Alert AIDI operations team
   - **If INVALID (ASYNC mode)**:
     - Deliver response (don't block)
     - Log error for post-call review
     - Alert if error rate exceeds threshold
   - **If UNKNOWN**: Treat as VALID (fail-open for availability) but log for investigation
8. **Response Delivery**: *(Modified)* Text-to-speech → Customer (only if validation passed in SYNC mode)
9. **Logging & Analytics**: *(Enhanced)* Save conversation + validation result to MongoDB

**Latency Impact**:
- **Synchronous Validation**: +300-500ms (total response time: 2.5-4.5 seconds)
- **Asynchronous Validation**: +0ms to customer (validation happens in background)

### Validation Adapter Architecture

**Component**: AIDI Validation Middleware

**Implementation**: Node.js/TypeScript middleware (compatible with AIDI's Lambda functions)

**Installation**: npm package `@hapyy/aidi-validation-adapter`

**Configuration** (example):
```typescript
import { HapyyValidator } from '@hapyy/aidi-validation-adapter';

const validator = new HapyyValidator({
  apiKey: process.env.HAPYY_API_KEY,
  endpoint: 'https://validation.hapyy.ai',
  mode: 'hybrid', // 'sync', 'async', or 'hybrid'
  timeout: 500, // ms for sync validation
  fallbackResponse: 'Let me verify that information for you...',
  routingRules: {
    // Define which conversation types use sync vs async
    sync: ['pricing_query', 'eligibility_check', 'claim_status'],
    async: ['general_info', 'faq', 'appointment_scheduling']
  }
});

// In AIDI's response handler
async function handleBotResponse(userQuery, botResponse, context) {
  // Classify conversation type (intent classifier)
  const conversationType = classifyIntent(userQuery);

  // Determine validation mode
  const validationMode = validator.getMode(conversationType);

  // Validate response
  const validationResult = await validator.validate({
    query: userQuery,
    response: botResponse,
    context: context,
    clientId: context.clientId,
    mode: validationMode
  });

  // Handle result
  if (validationMode === 'sync') {
    if (validationResult.status === 'INVALID') {
      // Block response, use fallback
      await alertOps(validationResult.explanation);
      return validator.getFallbackResponse(conversationType);
    } else if (validationResult.status === 'UNKNOWN') {
      // Log for investigation, allow response
      await logWarning(validationResult);
      return botResponse;
    } else {
      // Validation passed
      return botResponse;
    }
  } else {
    // Async mode: always return response, log validation result
    logValidationResult(validationResult);
    return botResponse;
  }
}
```

**Adapter Features**:
- **Intent Classification**: Automatically classify conversation type to determine sync vs async validation
- **Circuit Breaker**: If validation service is down (3 consecutive failures), switch to "monitor-only" mode and alert ops
- **Retry Logic**: Exponential backoff for transient failures (max 2 retries)
- **Caching**: Local cache for frequently validated patterns (1-hour TTL)
- **Metrics Collection**: Emit CloudWatch metrics for validation latency, success rate, error types
- **Fallback Responses**: Configurable fallback responses per conversation type when validation fails

### Validation Request Protocol

**API Endpoint**: `POST https://validation.hapyy.ai/v1/validate`

**Request Format** (JSON):
```json
{
  "conversation_id": "aidi_conv_abc123",
  "client_id": "innova_client_healthco",
  "timestamp": "2025-01-15T14:30:00Z",
  "validation_mode": "sync",
  "user_query": "What's the monthly premium for Plan A with a $500 deductible for a 45-year-old?",
  "bot_response": "The monthly premium would be $347 for Plan A with a $500 deductible.",
  "context": {
    "conversation_history": [
      {"role": "user", "content": "I'm looking for health insurance."},
      {"role": "assistant", "content": "I'd be happy to help! Are you looking for individual or family coverage?"},
      {"role": "user", "content": "Individual coverage for myself."}
    ],
    "user_profile": {
      "age": 45,
      "location": "California",
      "existing_conditions": []
    },
    "session_data": {
      "intent": "pricing_query",
      "entities_extracted": {
        "plan": "Plan A",
        "deductible": 500,
        "applicant_age": 45
      }
    }
  }
}
```

**Response Format** (JSON):
```json
{
  "validation_id": "val_xyz789",
  "status": "VALID",
  "confidence": 1.0,
  "latency_ms": 287,
  "timestamp": "2025-01-15T14:30:00.287Z",
  "explanation": "Premium calculation verified against HealthCo Plan A pricing table (version 2024-Q4). Formula: base_rate($285) + age_factor(45y: $62) = $347. VALID.",
  "validation_details": {
    "entities_validated": ["plan", "deductible", "premium_amount"],
    "knowledge_base_version": "healthco_kb_v2024q4",
    "solver_time_ms": 145,
    "cache_hit": false
  }
}
```

**Error Response** (JSON):
```json
{
  "validation_id": "val_xyz790",
  "status": "INVALID",
  "confidence": 1.0,
  "latency_ms": 312,
  "timestamp": "2025-01-15T14:35:00.312Z",
  "explanation": "Premium calculation ERROR. Expected $347, bot stated $247. Counterexample: HealthCo Plan A pricing table shows base_rate($285) + age_factor(45y: $62) = $347, NOT $247. INVALID.",
  "validation_details": {
    "error_type": "calculation_error",
    "entities_validated": ["plan", "deductible", "premium_amount"],
    "counterexample": {
      "expected_premium": 347,
      "stated_premium": 247,
      "error_magnitude": 100,
      "correct_calculation": "base_rate($285) + age_factor($62) = $347"
    },
    "knowledge_base_version": "healthco_kb_v2024q4",
    "solver_time_ms": 167,
    "cache_hit": false
  },
  "suggested_action": "BLOCK_RESPONSE",
  "fallback_response": "Let me verify that premium calculation for you. Please hold for a moment."
}
```

### Performance Requirements

**Latency Targets**:

| Validation Mode | Target Latency (P95) | Maximum Latency (P99) | Timeout |
|-----------------|----------------------|------------------------|---------|
| **Synchronous** | <500ms | <800ms | 1000ms |
| **Asynchronous** | <5s | <10s | 30s |

**Throughput Targets**:

| Deployment Phase | Validations/Day | Peak Rate | Infrastructure |
|------------------|-----------------|-----------|----------------|
| **Phase 1 (Pilot)** | 100-500 | 1/second | Shared dev cluster |
| **Phase 2 (Early Production)** | 1,000-5,000 | 10/second | Dedicated AIDI cluster (4 pods) |
| **Phase 3 (Full Production)** | 10,000-15,000 | 30/second | Auto-scaling cluster (8-16 pods) |
| **Future Scale** | 50,000-100,000 | 100/second | Multi-region (32-64 pods) |

**Availability Targets**:
- **Validation Service**: 99.9% uptime (43 minutes downtime/month)
- **Fail-Open Design**: If validation unavailable, AIDI continues operation with alerts
- **Degraded Mode**: Synchronous validation automatically falls back to asynchronous if latency exceeds threshold

### Client-Specific Knowledge Bases

**Multi-Tenant Knowledge Base Architecture**:

Each AIDI client has an isolated knowledge base containing:
- **Business Rules**: Pricing formulas, eligibility criteria, coverage limits
- **Policies**: Terms and conditions, exclusions, special provisions
- **Product Catalog**: Plans, features, pricing tiers
- **Regulatory Rules**: State-specific insurance regulations, HIPAA requirements
- **Historical Decisions**: Previously validated conversations for consistency

**Knowledge Base Schema** (example for HealthCo insurance client):

```yaml
client_id: innova_client_healthco
client_name: HealthCo Insurance
version: 2024-Q4
effective_date: 2024-10-01
expiration_date: 2025-01-01

products:
  - plan_id: plan_a
    plan_name: "Plan A - Bronze"
    coverage_type: individual
    pricing_formula:
      base_rate: 285
      age_factors:
        18-25: 0
        26-35: 25
        36-45: 62
        46-55: 120
        56-65: 180
      deductible_discounts:
        500: 0
        1000: -15
        2500: -35
        5000: -60
      state_multipliers:
        CA: 1.15
        NY: 1.25
        TX: 0.95
    eligibility_rules:
      min_age: 18
      max_age: 65
      excluded_conditions:
        - active_cancer
        - end_stage_renal_disease
    coverage_details:
      annual_max: 1000000
      out_of_pocket_max: 8000
      copay_primary_care: 30
      copay_specialist: 60

regulations:
  state: California
  aca_compliant: true
  requires_essential_benefits: true
  minimum_coverage_standards:
    - preventive_care
    - emergency_services
    - hospitalization
    - prescription_drugs

business_rules:
  quote_validity_days: 30
  enrollment_period: "11-01 to 01-31"
  effective_date_offset_days: 1
  cancellation_notice_days: 30
```

**Knowledge Base Loading**:
1. AIDI provides client configuration via API or Git repository
2. Hapyy validation team reviews and converts to SMT constraints
3. Knowledge base deployed to validation cluster with versioning
4. AIDI sends `client_id` with each validation request
5. Validation layer loads correct knowledge base version

**Knowledge Base Updates**:
- **Frequency**: Quarterly for pricing, ad-hoc for policy changes
- **Process**:
  1. Client provides updated rules (spreadsheet, API export, policy PDF)
  2. Hapyy team encodes rules as SMT constraints (1-2 days)
  3. Validation testing against historical conversations (1 day)
  4. Staged deployment: dev → staging → production (1 week)
  5. Rollback capability if validation success rate drops

**Version Control**:
- Git repository for each client's knowledge base
- Semantic versioning (e.g., `healthco_kb_v2024q4`)
- Validation requests specify knowledge base version or use "latest"
- Automatic expiration alerts (30 days before expiration)

## Real-Time Validation Flow

### Synchronous Validation (Critical Transactions)

**Use Cases**:
- Insurance premium quotes
- Eligibility determinations
- Claim status inquiries
- Coverage limit questions
- Policy cancellation confirmations

**Flow Diagram** (textual):

```
Customer Query → AIDI GPT-4 → Response Generated
                                      ↓
                        Validation Adapter (Classify Intent)
                                      ↓
                        [Is Critical Transaction?] → YES
                                      ↓
                        Validation Request (SYNC mode, timeout 500ms)
                                      ↓
                        Hapyy Validation Gateway
                                      ↓
                        ┌─────────────┴──────────────┐
                        ↓                            ↓
                Cache Check                   Symbolic Extraction
                [Redis]                       [NLP + Logic]
                        ↓                            ↓
                [Cache Hit?] → YES → Return Result
                        ↓ NO
                        ↓                            ↓
                        └─────────────┬──────────────┘
                                      ↓
                        SMT Validation (Z3 Solver, timeout 400ms)
                                      ↓
                        Result: VALID / INVALID / UNKNOWN
                                      ↓
                        ┌─────────────┼──────────────┐
                        ↓             ↓              ↓
                   [VALID]       [INVALID]      [UNKNOWN]
                        ↓             ↓              ↓
                Deliver Response  Block + Fallback  Deliver + Log
                        ↓             ↓              ↓
                   Customer ←────────┴──────────────┘
```

**Timing Breakdown** (target: <500ms total):
- Validation request serialization: 10ms
- Network latency (AIDI → Hapyy): 20ms
- Cache lookup: 5ms (cache hit) or proceed to validation
- Symbolic extraction: 80-150ms
- SMT solving: 100-250ms
- Result serialization: 10ms
- Network latency (Hapyy → AIDI): 20ms
- **Total**: 245-460ms (P95: 450ms)

**Error Handling**:
- **Timeout**: If validation exceeds 500ms, treat as UNKNOWN, deliver response, log delay
- **Service Unavailable**: Circuit breaker activates, switch to async mode, alert ops
- **Invalid Response**: Block delivery, use fallback ("Let me verify that..."), create support ticket

### Asynchronous Validation (Quality Monitoring)

**Use Cases**:
- General information queries (FAQs)
- Appointment scheduling
- Contact information requests
- Plan feature comparisons
- General advice (non-binding)

**Flow Diagram** (textual):

```
Customer Query → AIDI GPT-4 → Response Generated
                                      ↓
                        Validation Adapter (Classify Intent)
                                      ↓
                        [Is Critical Transaction?] → NO
                                      ↓
                        Deliver Response to Customer (immediate)
                                      ↓
                        Validation Request (ASYNC mode, no timeout)
                                      ↓
                        Kafka Queue (topic: aidi_async_validations)
                                      ↓
                        Validation Worker Pool (background processing)
                                      ↓
                        Symbolic Extraction + SMT Validation
                                      ↓
                        Result Stored in InfluxDB
                                      ↓
                        ┌─────────────┴──────────────┐
                        ↓                            ↓
                 [Validation Failed]          [Validation Passed]
                        ↓                            ↓
                 Alert Dashboard              Update Metrics
                 (if error rate > 5%)         (success rate, latency)
                        ↓                            ↓
                 Quality Review Queue          Analytics Dashboard
```

**Batch Processing**:
- Conversations batched every 5 minutes (e.g., 100 conversations)
- Kafka partitions across 8 validation workers
- Each worker processes 12-13 conversations in parallel
- Results aggregated and written to InfluxDB
- Dashboard updates every 5 minutes with latest metrics

**Alerting Thresholds**:
- **Critical**: Error rate >10% for any client in 15-minute window → PagerDuty alert
- **High**: Error rate >5% for any client in 1-hour window → Slack alert
- **Medium**: Specific error pattern detected (e.g., 10 failures for same business rule) → Email alert
- **Low**: Daily digest of all validation failures → Email to client success team

## Business Rule Compliance Checking

### Regulatory Compliance Rules

**HIPAA Compliance** (healthcare clients):
- **PHI Detection**: Identify if bot response contains Protected Health Information without proper consent
- **Minimum Necessary Rule**: Verify bot only discloses information necessary to answer query
- **Access Control**: Ensure bot only accesses patient data within authorization scope

**Example Validation**:
- User query: "What's my recent lab result?"
- Bot response: "Your hemoglobin A1C from 1/10/2025 was 6.2%"
- Validation check: Was patient authenticated? Is requester the patient or authorized representative?
- If authorization missing: INVALID → Block response or request authentication

**PCI Compliance** (financial services clients):
- **No Credit Card Storage**: Verify bot never logs or repeats full credit card numbers
- **Secure Data Handling**: Check that payment information is tokenized
- **Cardholder Data Environment**: Ensure bot directs payment to PCI-compliant system

**GDPR Compliance** (EU clients):
- **Right to Erasure**: Flag conversations containing personal data for deletion upon request
- **Data Minimization**: Verify bot collects only necessary personal information
- **Consent Verification**: Check that data processing has legal basis

### Business Policy Compliance

**Pricing Policy Enforcement**:
- **Discount Authorization**: Verify discounts are within authorized limits (e.g., max 20% off)
- **Pricing Consistency**: Ensure quoted price matches current pricing table
- **Promotional Eligibility**: Validate customer qualifies for promotional pricing

**Coverage Limit Validation**:
- **Annual Maximums**: Verify claim doesn't exceed annual coverage limit
- **Per-Incident Limits**: Check individual claim is within per-incident maximum
- **Lifetime Limits**: Ensure cumulative claims don't exceed lifetime maximum (where applicable)

**Operational Policy Checks**:
- **Business Hours**: Verify bot doesn't promise same-day service outside business hours
- **Service Area**: Check customer location is within service area
- **Eligibility Periods**: Validate customer is within enrollment or claims period

## Dashboard Integration

### AIDI Dashboard Architecture

**Current Dashboard** (Innova's existing AIDI analytics):
- **Framework**: React + TypeScript
- **Backend**: GraphQL API (Apollo Server on AWS Lambda)
- **Database**: MongoDB for conversation data, CloudWatch for metrics
- **Charts**: Recharts library for visualizations
- **Deployment**: S3 + CloudFront for static hosting

**Current Metrics Displayed**:
- Total calls per day/week/month
- Average call duration
- Most common intents
- Customer satisfaction scores (CSAT from post-call surveys)
- Call volume by client

### Enhanced Dashboard with Validation Metrics

**New Metrics Section**: "Quality & Validation"

**Real-Time Metrics**:
- **Validation Rate**: Percentage of conversations validated (target: 100%)
  - Gauge visualization (0-100%)
  - Current: 98.7% (15 minutes)
- **Validation Success Rate**: Percentage passing validation (target: >95%)
  - Gauge visualization (0-100%)
  - Current: 96.2% (15 minutes)
- **Average Validation Latency**: P50/P95/P99 latency for sync validations
  - Line chart (last 24 hours)
  - Current P95: 387ms
- **Active Alerts**: Count of unresolved validation failures
  - Number with severity badges
  - Current: 3 (2 medium, 1 low)

**Historical Trends** (last 30 days):
- **Validation Success Rate Over Time**: Line chart showing daily success rate
- **Error Category Breakdown**: Pie chart or bar chart
  - Hallucination: 45%
  - Calculation Error: 30%
  - Policy Violation: 15%
  - Logic Inconsistency: 10%
- **Top Failing Conversation Types**: Table showing intents with lowest success rates
  - Pricing queries: 94.2% success
  - Eligibility checks: 97.8% success
  - Coverage limits: 95.1% success

**Per-Client Breakdown** (for Innova to monitor their clients):
- Client name dropdown selector
- Client-specific validation metrics
- Comparison to overall average
- Client-specific error patterns

**Drill-Down Capabilities**:
- Click on error count → View list of failed validations
- Click on specific failure → View full conversation, expected vs actual response, counterexample
- Export failed conversations for quality review (CSV or JSON)

### GraphQL Schema Extension

**New Types**:
```graphql
type ValidationMetrics {
  validationRate: Float!
  successRate: Float!
  latencyP50: Int!
  latencyP95: Int!
  latencyP99: Int!
  totalValidations: Int!
  activeAlerts: Int!
  timestamp: DateTime!
}

type ValidationError {
  validationId: ID!
  conversationId: ID!
  clientId: ID!
  timestamp: DateTime!
  errorType: ErrorType!
  userQuery: String!
  botResponse: String!
  expectedResponse: String
  explanation: String!
  severity: Severity!
}

enum ErrorType {
  HALLUCINATION
  CALCULATION_ERROR
  POLICY_VIOLATION
  LOGIC_INCONSISTENCY
  UNKNOWN
}

enum Severity {
  CRITICAL
  HIGH
  MEDIUM
  LOW
}

type ValidationTrend {
  date: Date!
  successRate: Float!
  totalValidations: Int!
  errorBreakdown: [ErrorBreakdown!]!
}

type ErrorBreakdown {
  errorType: ErrorType!
  count: Int!
  percentage: Float!
}

extend type Query {
  validationMetrics(
    clientId: ID
    timeRange: TimeRange!
  ): ValidationMetrics!

  validationErrors(
    clientId: ID
    errorType: ErrorType
    severity: Severity
    limit: Int = 100
    offset: Int = 0
  ): [ValidationError!]!

  validationTrends(
    clientId: ID
    startDate: Date!
    endDate: Date!
  ): [ValidationTrend!]!
}

enum TimeRange {
  LAST_15_MIN
  LAST_HOUR
  LAST_24_HOURS
  LAST_7_DAYS
  LAST_30_DAYS
}
```

**Implementation**:
- GraphQL resolvers query InfluxDB for validation metrics
- AIDI's existing MongoDB stores conversation data with validation results
- Hapyy provides read-only database connection or API endpoint for metrics

### Embedded Validation Dashboard Component

**React Component**: `<ValidationDashboard />`

**Installation**: npm package `@hapyy/aidi-validation-dashboard`

**Usage**:
```tsx
import { ValidationDashboard } from '@hapyy/aidi-validation-dashboard';

function AIDIDashboard() {
  return (
    <div>
      {/* Existing AIDI dashboard components */}
      <CallVolumeChart />
      <IntentDistribution />
      <CustomerSatisfaction />

      {/* New validation quality section */}
      <ValidationDashboard
        clientId={selectedClient}
        timeRange="LAST_24_HOURS"
        apiEndpoint="https://validation.hapyy.ai/api/dashboard"
        apiKey={hapyyApiKey}
        theme="light" // or "dark" to match AIDI's theme
      />
    </div>
  );
}
```

**Component Features**:
- Auto-refresh metrics every 15 seconds (real-time mode)
- Manual refresh button
- Export functionality (CSV, JSON, PDF report)
- Drill-down modals for failed validations
- Responsive design (desktop, tablet, mobile)

## Deployment Architecture

### Co-Location Strategy

**Objective**: Minimize network latency by deploying validation infrastructure in same AWS region as AIDI

**AIDI Infrastructure**:
- **Primary Region**: us-east-1 (N. Virginia)
- **Secondary Region**: us-west-2 (Oregon)
- **Hosting**: AWS Lambda (serverless)

**Hapyy Validation Infrastructure**:
- **Deployment Model**: Kubernetes cluster in same VPC as AIDI Lambda functions
- **Primary Region**: us-east-1 (matches AIDI)
- **Secondary Region**: us-west-2 (DR and load balancing)

**Network Architecture**:
```
AIDI Lambda Functions (us-east-1)
         ↓
VPC Peering or PrivateLink
         ↓
Hapyy Validation Cluster (us-east-1)
  - API Gateway (Kong) on NLB
  - Validation Workers (K8s pods)
  - Z3 Solver Pool (K8s pods)
  - Redis Cache (ElastiCache)
  - PostgreSQL Knowledge Base (RDS)
```

**Latency Optimization**:
- **VPC PrivateLink**: Private network connection (no internet egress)
- **Network Load Balancer**: Layer 4 load balancing for minimal overhead (<5ms)
- **Connection Pooling**: Reuse HTTP connections between AIDI and validation gateway
- **Regional Routing**: Route validation requests to same-region cluster

**Expected Latency**:
- Lambda → Validation Gateway: 10-20ms (vs 50-100ms over public internet)
- Total validation latency reduced by 40-80ms

### Scaling Strategy

**Phase 1 - Pilot (100-500 validations/day)**:
- **Cluster Size**: 4 nodes (t3.large: 2 vCPU, 8GB RAM each)
- **Pods**:
  - 2 API Gateway pods
  - 4 Validation Worker pods
  - 4 Z3 Solver pods
  - 1 Redis pod
- **Database**: db.t3.medium RDS PostgreSQL (2 vCPU, 4GB RAM)
- **Cost**: ~$400/month

**Phase 2 - Early Production (1,000-5,000 validations/day)**:
- **Cluster Size**: 8 nodes (t3.xlarge: 4 vCPU, 16GB RAM each)
- **Pods**:
  - 4 API Gateway pods
  - 8 Validation Worker pods
  - 8 Z3 Solver pods
  - 2 Redis pods (master + replica)
- **Database**: db.r6g.large RDS PostgreSQL (2 vCPU, 16GB RAM)
- **Cost**: ~$1,200/month

**Phase 3 - Full Production (10,000-15,000 validations/day)**:
- **Cluster Size**: 16 nodes (c6i.2xlarge: 8 vCPU, 16GB RAM each)
- **Pods**:
  - 8 API Gateway pods (auto-scale 4-16)
  - 16 Validation Worker pods (auto-scale 8-32)
  - 16 Z3 Solver pods (auto-scale 8-32)
  - 3 Redis pods (master + 2 replicas)
- **Database**: db.r6g.xlarge RDS PostgreSQL (4 vCPU, 32GB RAM) with read replica
- **Cost**: ~$3,000/month

**Auto-Scaling Policies**:
- **Trigger**: Queue depth > 50 validations OR P95 latency > 600ms
- **Scale Up**: Add 25% more pods (e.g., 16 → 20 workers)
- **Scale Down**: Remove 25% pods if utilization < 30% for 10 minutes
- **Limits**: Min 8 pods, max 64 pods per component

### Disaster Recovery

**Failover Strategy**:
- **Primary Region Down**: Automatically route validation traffic to us-west-2 (Route 53 health checks)
- **Database Failover**: RDS Multi-AZ automatic failover (<2 minutes)
- **Knowledge Base Sync**: Real-time replication to secondary region
- **Cache Warming**: Pre-populate us-west-2 cache with common validation patterns

**Backup Strategy**:
- **Knowledge Base**: Daily automated backups to S3 (30-day retention)
- **Configuration**: Git repository for infrastructure-as-code (Terraform, Helm charts)
- **Validation Logs**: Streamed to S3 for compliance (7-year retention)

**Recovery Time Objective (RTO)**: 15 minutes (automated failover)
**Recovery Point Objective (RPO)**: 5 minutes (real-time replication)

## Migration & Rollout Plan

### Phase 1: Pilot Integration (Weeks 1-4)

**Objective**: Validate integration architecture with minimal risk

**Scope**:
- 1 AIDI client (volunteer, non-critical)
- Asynchronous validation only (no blocking)
- 100-500 validations/day
- Dev/staging environment only

**Tasks**:
1. **Week 1**: Infrastructure setup
   - Deploy validation cluster in AIDI's AWS account (us-east-1)
   - Configure VPC peering and security groups
   - Set up monitoring and alerting
2. **Week 2**: Knowledge base creation
   - Workshop with pilot client to document business rules
   - Encode rules as SMT constraints
   - Load knowledge base and validate with test conversations
3. **Week 3**: AIDI integration
   - Install `@hapyy/aidi-validation-adapter` in AIDI codebase
   - Configure for async-only mode
   - Deploy to staging environment
   - Run integration tests (100 synthetic conversations)
4. **Week 4**: Pilot launch and monitoring
   - Enable validation for pilot client in staging
   - Monitor performance, accuracy, and error rates
   - Collect feedback from Innova and pilot client
   - Tune validation rules and performance

**Success Criteria**:
- Validation rate >95% (at least 95 of 100 conversations validated)
- Zero impact on AIDI latency (async mode)
- Validation success rate >80% (expected low initially, will improve with tuning)
- No production incidents

### Phase 2: Production Rollout (Weeks 5-8)

**Objective**: Expand to multiple clients with hybrid validation mode

**Scope**:
- 5 AIDI clients (mix of healthcare, insurance, financial services)
- Hybrid validation: Async for all, sync for pricing queries only
- 1,000-5,000 validations/day
- Production environment

**Tasks**:
1. **Week 5**: Multi-client knowledge bases
   - Create knowledge bases for 4 additional clients
   - Implement multi-tenant data isolation
   - Set up per-client dashboards
2. **Week 6**: Sync validation enablement
   - Configure routing rules for pricing queries (sync mode)
   - Implement fallback response logic
   - Deploy to production with feature flag (disabled by default)
3. **Week 7**: Staged production enablement
   - Enable async validation for all 5 clients
   - Enable sync validation for 1 client (most mature knowledge base)
   - Monitor latency impact (<500ms P95)
4. **Week 8**: Full production validation
   - Enable sync validation for remaining 4 clients
   - Tune performance based on production load
   - Train AIDI ops team on validation dashboard and alerts

**Success Criteria**:
- Validation rate >98%
- Validation success rate >90%
- Sync validation latency P95 <500ms
- No customer complaints due to validation-related delays
- Zero false positives blocking valid responses

### Phase 3: Full Deployment (Weeks 9-12)

**Objective**: Scale to all AIDI clients with comprehensive validation

**Scope**:
- All 15-20 AIDI clients
- Sync validation for all critical transaction types
- 10,000-15,000 validations/day
- Full dashboard integration

**Tasks**:
1. **Week 9-10**: Remaining client onboarding
   - Create knowledge bases for all remaining clients
   - Batch onboarding (3-4 clients per week)
   - Automated knowledge base setup tools
2. **Week 11**: Full sync validation coverage
   - Expand sync validation to all critical transaction types:
     - Pricing queries
     - Eligibility checks
     - Coverage limit questions
     - Claim status inquiries
   - Fine-tune routing rules per client
3. **Week 12**: Dashboard and reporting
   - Embed validation dashboard in AIDI's main dashboard
   - Configure automated compliance reports (weekly, monthly)
   - Train client success team on validation metrics and insights
   - Document best practices and troubleshooting guide

**Success Criteria**:
- All AIDI clients using validation (100% coverage)
- Validation success rate >95%
- Sync validation latency P95 <500ms consistently
- Customer satisfaction maintained or improved (no impact from validation)
- Measurable reduction in customer complaints (target: 50% reduction)

### Ongoing Operations

**Knowledge Base Maintenance**:
- **Quarterly Updates**: Scheduled updates for pricing, policy changes
- **Ad-Hoc Updates**: Emergency updates for critical rule changes (same-day deployment)
- **Version Control**: All changes tracked in Git with approval workflow
- **Regression Testing**: Automated tests run on every knowledge base update

**Performance Monitoring**:
- **Daily Reviews**: Ops team reviews validation metrics dashboard
- **Weekly Reports**: Automated email with key metrics and trends
- **Monthly Business Reviews**: Joint review with Innova leadership on quality improvements

**Continuous Improvement**:
- **Error Analysis**: Monthly review of validation failures to identify patterns
- **Rule Refinement**: Quarterly review of knowledge base accuracy
- **Feature Requests**: Collect feedback from AIDI clients for new validation capabilities

## Security & Compliance

### Data Privacy

**PII Handling**:
- Validation requests contain conversation data (may include PII)
- **Storage**: Validation logs encrypted at rest (AES-256)
- **Retention**: 90 days default, configurable to 7-365 days per client
- **Anonymization**: Option to strip PII from logs before storage (regex-based redaction)
- **Access Control**: Only AIDI and client administrators can view validation logs

**HIPAA Compliance** (healthcare clients):
- **BAA Required**: Business Associate Agreement between Hapyy and Innova
- **Encryption**: TLS 1.3 in transit, AES-256 at rest
- **Audit Logging**: All access to validation data logged with user identity
- **Access Control**: Role-based access, MFA required for admin access
- **Data Residency**: Option to deploy validation cluster in client's own AWS account

### API Security

**Authentication**:
- **API Keys**: HMAC-SHA256 signed requests
- **Key Rotation**: Automated quarterly rotation with 30-day overlap
- **Scope Limiting**: API keys scoped to specific clients and permissions

**Rate Limiting**:
- **Free Tier**: 1,000 validations/day, 10 requests/second
- **Enterprise Tier**: Unlimited validations, 100 requests/second
- **Burst Allowance**: 2x sustained rate for 10 seconds

**Network Security**:
- **VPC PrivateLink**: Private connection, no internet exposure
- **Security Groups**: Whitelist AIDI Lambda security group only
- **TLS Mutual Authentication**: Optional mTLS for highest security clients

### Compliance Reporting

**Automated Reports**:
- **Daily**: Validation summary (total, success rate, error breakdown)
- **Weekly**: Quality trends, top errors, knowledge base changes
- **Monthly**: Compliance report (HIPAA violations, policy breaches)
- **Quarterly**: Executive summary (business impact, ROI, recommendations)

**Export Formats**:
- PDF for executive review
- CSV for data analysis
- JSON for programmatic access

## Cost Model

### Infrastructure Costs

**Hapyy's Hosting Costs** (10,000 validations/day baseline):
- Kubernetes cluster: $1,200/month
- Database (RDS): $400/month
- Cache (ElastiCache): $150/month
- Data transfer: $100/month
- Monitoring (CloudWatch, Prometheus): $50/month
- **Total**: $1,900/month

### Pricing Model for AIDI

**Option 1: Per-Validation Pricing**
- $0.05 per validation (sync or async)
- 10,000 validations/day = $500/day = $15,000/month
- Discounts:
  - >50,000 validations/day: $0.03 per validation
  - >100,000 validations/day: $0.02 per validation

**Option 2: Subscription Pricing**
- **Starter**: $5,000/month (up to 5,000 validations/day, 2 clients)
- **Professional**: $12,000/month (up to 15,000 validations/day, 10 clients)
- **Enterprise**: $25,000/month (up to 50,000 validations/day, unlimited clients)
- Overage: $0.03 per validation beyond tier limit

**Option 3: Revenue Share**
- Hapyy charges Innova 15-20% of incremental revenue attributable to validation
- Innova charges their clients premium pricing for "validated AI" tier
- Example: If client pays $2,000/month extra for validation, Hapyy receives $300-400/month

**Recommended for AIDI**: Option 2 (Subscription) for predictable costs, with Option 3 (Revenue Share) for strategic partnership alignment

## References

1. **API Integration Patterns**:
   - Hohpe, G., & Woolf, B. (2003). "Enterprise Integration Patterns". Addison-Wesley.
   - "AWS Lambda Best Practices". https://docs.aws.amazon.com/lambda/latest/dg/best-practices.html

2. **Real-Time Validation Architecture**:
   - Kleppmann, M. (2017). "Designing Data-Intensive Applications". O'Reilly Media.
   - "Stream Processing with Apache Kafka". https://kafka.apache.org/documentation/streams/

3. **Multi-Tenancy Design**:
   - Chong, F., et al. (2006). "Multi-Tenant Data Architecture". Microsoft Architecture Journal.
   - "AWS SaaS Lens - Well-Architected Framework". https://docs.aws.amazon.com/wellarchitected/latest/saas-lens/

4. **Performance Optimization**:
   - Gregg, B. (2020). "Systems Performance: Enterprise and the Cloud". Addison-Wesley.
   - "Redis Best Practices". https://redis.io/topics/optimization

5. **Knowledge Base Management**:
   - "Semantic Web Technologies for Enterprise Application Integration". W3C.
   - "Business Rules Management Systems". Business Rules Group.

6. **Dashboard Design**:
   - Few, S. (2006). "Information Dashboard Design". O'Reilly Media.
   - "GraphQL Best Practices". https://graphql.org/learn/best-practices/

7. **Cloud Architecture**:
   - "AWS Well-Architected Framework". https://aws.amazon.com/architecture/well-architected/
   - "Kubernetes Production Patterns". https://kubernetes.io/docs/concepts/

8. **HIPAA Compliance**:
   - "HIPAA Security Rule". U.S. Department of Health & Human Services.
   - "AWS HIPAA Compliance Whitepaper". https://aws.amazon.com/compliance/hipaa-compliance/