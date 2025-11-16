# Client Services Platform Architecture

**Research Date**: January 2025
**Sprint**: 02 - Conversational AI Quality Assurance
**Task**: 03 - Solution Architecture Design
**Researcher**: Solution Architect Skill

## Executive Summary

The Client Services Platform transforms raw validation data into actionable business intelligence, providing Innova and their clients with real-time visibility into conversational AI quality through intuitive dashboards, automated alerting, compliance reporting, and trend analytics. This platform is the customer-facing layer that demonstrates the business value of mathematical validation, translating technical metrics (SAT/UNSAT results, solving latency, cache hit rates) into business KPIs (response accuracy rate, prevented errors, cost savings, compliance adherence).

The business value proposition is multifaceted: enable Innova to differentiate AIDI with quantifiable quality guarantees, provide clients with confidence in their AI-powered customer service, generate compliance reports automatically for auditors, and identify quality issues proactively before they escalate to customer complaints. For regulated industries (healthcare, finance, insurance), the platform's audit trail and compliance dashboards are mission-critical for HIPAA, SOC 2, and industry-specific certifications.

The architecture emphasizes multi-tenant SaaS design with strict data isolation, real-time analytics using time-series databases and streaming aggregation, role-based access control for hierarchical organizations, and white-label customization for Innova to brand as their own. The platform scales to support thousands of concurrent users viewing dashboards, with sub-second query response times and 99.9% uptime.

## Key Design Decisions

- **Multi-Tenant SaaS Architecture**: Shared infrastructure with logical data isolation per client, enabling cost efficiency while maintaining security
- **Real-Time Analytics Pipeline**: Kafka streams for event ingestion, InfluxDB for time-series metrics, ClickHouse for OLAP queries, enabling dashboards to update every 5-15 seconds
- **GraphQL API**: Flexible query language allowing dashboard to fetch exactly the data needed, reducing over-fetching and improving performance
- **React Dashboard**: Modern, responsive web application with real-time updates via WebSockets
- **Role-Based Access Control (RBAC)**: Hierarchical permissions (System Admin → Client Admin → Department Manager → Analyst) with fine-grained resource access
- **White-Label Customization**: Configurable branding (logo, colors, domain) for Innova to present as AIDI feature
- **Compliance-First Reporting**: Pre-built report templates for HIPAA, SOC 2, ISO 27001, with automated generation and PDF export
- **Alert Routing**: Configurable alert channels (email, Slack, PagerDuty, webhooks) with escalation policies
- **Export Capabilities**: CSV, JSON, PDF exports for offline analysis and archival

## Platform Architecture

### Component Overview

**Textual Architecture Diagram**:

```
┌─────────────────────────────────────────────────────────────────┐
│                         CLIENT USERS                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │  Executive   │  │  Operations  │  │  Compliance Officer  │  │
│  │  Dashboard   │  │  Dashboard   │  │  Reports             │  │
│  └──────┬───────┘  └──────┬───────┘  └──────────┬───────────┘  │
└─────────┼──────────────────┼─────────────────────┼──────────────┘
          │                  │                     │
          │ HTTPS            │ HTTPS               │ HTTPS
          │                  │                     │
┌─────────▼──────────────────▼─────────────────────▼──────────────┐
│                     WEB APPLICATION LAYER                        │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ React Frontend (SPA)                                     │  │
│  │  - Real-time dashboards (recharts, D3.js)               │  │
│  │  - WebSocket client for live updates                    │  │
│  │  - Material-UI components                                │  │
│  │  - Authentication (OAuth 2.0)                            │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│                       API GATEWAY LAYER                          │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Kong API Gateway                                         │  │
│  │  - Authentication (JWT validation)                       │  │
│  │  - Rate limiting (1000 req/min per user)                │  │
│  │  - Request routing                                       │  │
│  │  - CORS handling                                         │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│                     GRAPHQL API LAYER                            │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Apollo Server (Node.js)                                  │  │
│  │  - GraphQL schema and resolvers                          │  │
│  │  - DataLoader for batch/cache optimization               │  │
│  │  - Subscriptions for real-time updates                   │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
                    ┌────────────┴────────────┐
                    │                         │
┌───────────────────▼──────────┐  ┌───────────▼───────────────────┐
│    ANALYTICS SERVICE          │  │   REPORTING SERVICE           │
│  ┌──────────────────────┐    │  │  ┌──────────────────────┐    │
│  │ Query Engine         │    │  │  │ Report Generator     │    │
│  │ (ClickHouse, Influx) │    │  │  │ (PDF, CSV, JSON)     │    │
│  └──────────────────────┘    │  │  └──────────────────────┘    │
└───────────┬──────────────────┘  └───────────┬──────────────────┘
            │                                  │
┌───────────▼──────────────────────────────────▼──────────────────┐
│                      DATA STORAGE LAYER                          │
│  ┌──────────────┐  ┌───────────────┐  ┌─────────────────────┐  │
│  │  InfluxDB    │  │  ClickHouse   │  │  PostgreSQL         │  │
│  │  (Metrics)   │  │  (Analytics)  │  │  (User, Config)     │  │
│  └──────┬───────┘  └───────┬───────┘  └──────────┬──────────┘  │
└─────────┼──────────────────┼─────────────────────┼──────────────┘
          │                  │                     │
┌─────────▼──────────────────▼─────────────────────▼──────────────┐
│                  DATA INGESTION LAYER                            │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Apache Kafka (Event Streaming)                           │  │
│  │  - Topic: validation_results                             │  │
│  │  - Topic: alert_events                                   │  │
│  │  - Topic: user_actions                                   │  │
│  └────────────────────────────┬─────────────────────────────┘  │
│  ┌────────────────────────────▼─────────────────────────────┐  │
│  │ Stream Processors (Kafka Streams)                        │  │
│  │  - Aggregate metrics (5-min windows)                     │  │
│  │  - Detect anomalies (error rate spikes)                  │  │
│  │  - Trigger alerts                                        │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│                      ALERTING LAYER                              │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Alert Manager                                            │  │
│  │  - Rule evaluation (error rate > 5%)                     │  │
│  │  - Alert routing (email, Slack, PagerDuty)               │  │
│  │  - Deduplication and grouping                            │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

### Multi-Tenant Data Model

**Purpose**: Isolate client data while sharing infrastructure

**Data Isolation Strategies**:

**1. Database Schema per Tenant** (PostgreSQL for user management):
```sql
-- Shared users table with tenant_id
CREATE TABLE users (
    id UUID PRIMARY KEY,
    email VARCHAR(255) UNIQUE NOT NULL,
    tenant_id UUID NOT NULL,
    role VARCHAR(50) NOT NULL,
    FOREIGN KEY (tenant_id) REFERENCES tenants(id)
);

-- Row-level security policy
ALTER TABLE users ENABLE ROW LEVEL SECURITY;

CREATE POLICY tenant_isolation ON users
    FOR ALL
    USING (tenant_id = current_setting('app.current_tenant')::UUID);
```

**2. Tenant Tagging** (InfluxDB for time-series metrics):
```
validation_results,tenant=healthco,intent=pricing_query success_rate=0.96 1642267200
validation_results,tenant=autoinsure,intent=pricing_query success_rate=0.94 1642267200
```

**3. Tenant Partitioning** (ClickHouse for analytics):
```sql
-- Partition by tenant_id for query performance
CREATE TABLE validation_history (
    timestamp DateTime,
    tenant_id String,
    validation_id String,
    status String,
    latency_ms UInt32
) ENGINE = MergeTree()
PARTITION BY (toYYYYMM(timestamp), tenant_id)
ORDER BY (timestamp, validation_id);
```

### Real-Time Analytics Pipeline

**Data Flow**:

1. **Validation Completed** → Publish event to Kafka topic `validation_results`
   ```json
   {
     "validation_id": "val_123",
     "tenant_id": "healthco",
     "timestamp": "2025-01-15T14:30:00Z",
     "status": "VALID",
     "latency_ms": 287,
     "intent": "pricing_query",
     "error_type": null
   }
   ```

2. **Kafka Stream Processor** → Aggregate metrics (5-minute tumbling windows)
   ```python
   # Kafka Streams topology
   stream = builder.stream('validation_results')

   # Aggregate success rate per tenant per 5 minutes
   aggregated = stream \
       .groupBy(lambda k, v: v['tenant_id']) \
       .windowedBy(TimeWindows.of(timedelta(minutes=5))) \
       .aggregate(
           initializer=lambda: {'total': 0, 'success': 0},
           aggregator=lambda key, value, aggregate: {
               'total': aggregate['total'] + 1,
               'success': aggregate['success'] + (1 if value['status'] == 'VALID' else 0)
           }
       )
   ```

3. **Write to InfluxDB** → Store aggregated metrics
   ```python
   influx_client.write_points([{
       'measurement': 'validation_metrics',
       'tags': {
           'tenant': 'healthco',
           'window': '5min'
       },
       'time': timestamp,
       'fields': {
           'success_rate': 0.96,
           'total_validations': 250,
           'avg_latency_ms': 320
       }
   }])
   ```

4. **Dashboard Query** → Fetch real-time metrics
   ```javascript
   // GraphQL query
   query {
     validationMetrics(
       tenantId: "healthco",
       timeRange: LAST_24_HOURS,
       interval: FIVE_MINUTES
     ) {
       timestamp
       successRate
       totalValidations
       avgLatencyMs
     }
   }
   ```

5. **WebSocket Push** → Push updates to connected dashboards
   ```javascript
   subscription {
     validationMetricsUpdated(tenantId: "healthco") {
       successRate
       totalValidations
       avgLatencyMs
     }
   }
   ```

**Latency**: Dashboard updates within 5-15 seconds of validation completion

### Dashboard Features

**Executive Dashboard**:

**Metrics Displayed**:
- **Validation Success Rate** (current, 24h, 7d, 30d): Gauge showing 96.2%
- **Total Validations Today**: Counter showing 10,437
- **Error Trend**: Line chart showing error rate over last 7 days
- **Cost Savings**: Calculated metric showing "Prevented 412 errors = $82,400 saved"
- **Top Error Categories**: Pie chart (Hallucination 45%, Calculation Error 30%, Policy Violation 15%, Other 10%)

**Visual Layout** (textual):
```
┌─────────────────────────────────────────────────────────────────┐
│  Executive Dashboard                          [Last 24 Hours ▼] │
├─────────────────────────────────────────────────────────────────┤
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │  Success     │  │  Validations │  │  Cost Savings        │  │
│  │  Rate        │  │  Today       │  │  (Prevented Errors)  │  │
│  │              │  │              │  │                      │  │
│  │    96.2%     │  │   10,437     │  │    $82,400           │  │
│  │  ━━━━━━━━━   │  │   +15% ↑    │  │    412 errors        │  │
│  └──────────────┘  └──────────────┘  └──────────────────────┘  │
├─────────────────────────────────────────────────────────────────┤
│  Error Rate Trend (Last 7 Days)                                 │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ 5% ┤                                                      │  │
│  │ 4% ┤            ╭─╮                                       │  │
│  │ 3% ┤        ╭───╯ ╰──╮                                   │  │
│  │ 2% ┤    ╭───╯        ╰───╮                               │  │
│  │ 1% ┤────╯                ╰───────────────────────────    │  │
│  │    └─────┬──────┬──────┬──────┬──────┬──────┬──────      │  │
│  │        Mon    Tue    Wed    Thu    Fri    Sat    Sun     │  │
│  └──────────────────────────────────────────────────────────┘  │
├─────────────────────────────────────────────────────────────────┤
│  Top Error Categories                Validation by Intent      │
│  ┌─────────────────────────┐      ┌──────────────────────────┐│
│  │   Hallucination  45%    │      │ Pricing Query    3,245   ││
│  │   Calculation    30%    │      │ Eligibility      2,876   ││
│  │   Policy Viol.   15%    │      │ Coverage Inquiry 2,103   ││
│  │   Other          10%    │      │ Claim Status     1,987   ││
│  └─────────────────────────┘      └──────────────────────────┘│
└─────────────────────────────────────────────────────────────────┘
```

**Operations Dashboard**:

**Metrics Displayed**:
- **Real-Time Validation Queue**: Current queue depth, processing rate
- **Performance**: P50/P95/P99 latency, cache hit rate
- **System Health**: API uptime, solver pool utilization, alert count
- **Recent Failed Validations**: Table with conversation ID, error type, timestamp, action

**Compliance Dashboard**:

**Metrics Displayed**:
- **HIPAA Compliance Score**: Automated assessment based on validation rules
- **Audit Log**: Searchable table of all validation decisions
- **Regulatory Violations**: Count and details of HIPAA/PCI/GDPR violations detected
- **Compliance Reports**: Pre-generated monthly reports (PDF download)

### GraphQL API Schema

**Core Types**:
```graphql
type ValidationMetrics {
  timestamp: DateTime!
  successRate: Float!
  totalValidations: Int!
  avgLatencyMs: Int!
  errorBreakdown: [ErrorBreakdown!]!
}

type ErrorBreakdown {
  errorType: ErrorType!
  count: Int!
  percentage: Float!
}

enum ErrorType {
  HALLUCINATION
  CALCULATION_ERROR
  POLICY_VIOLATION
  LOGIC_INCONSISTENCY
  UNKNOWN
}

type ValidationDetail {
  validationId: ID!
  conversationId: ID!
  timestamp: DateTime!
  status: ValidationStatus!
  intent: String!
  userQuery: String!
  botResponse: String!
  explanation: String
  counterexample: JSON
  latencyMs: Int!
}

enum ValidationStatus {
  VALID
  INVALID
  UNKNOWN
}

type Tenant {
  id: ID!
  name: String!
  industry: String!
  validationStats: ValidationMetrics!
}

type Alert {
  id: ID!
  severity: Severity!
  message: String!
  triggeredAt: DateTime!
  resolvedAt: DateTime
  validationIds: [ID!]!
}

enum Severity {
  CRITICAL
  HIGH
  MEDIUM
  LOW
}
```

**Queries**:
```graphql
type Query {
  # Get aggregated metrics
  validationMetrics(
    tenantId: ID!
    timeRange: TimeRange!
    interval: Interval
  ): [ValidationMetrics!]!

  # Get validation details
  validationDetails(
    tenantId: ID!
    filters: ValidationFilters
    limit: Int = 100
    offset: Int = 0
  ): [ValidationDetail!]!

  # Get active alerts
  alerts(
    tenantId: ID!
    severity: Severity
    resolved: Boolean
  ): [Alert!]!

  # Get tenant info
  tenant(id: ID!): Tenant

  # Generate compliance report
  complianceReport(
    tenantId: ID!
    reportType: ReportType!
    startDate: Date!
    endDate: Date!
  ): Report!
}

enum TimeRange {
  LAST_15_MIN
  LAST_HOUR
  LAST_24_HOURS
  LAST_7_DAYS
  LAST_30_DAYS
  CUSTOM
}

enum Interval {
  ONE_MINUTE
  FIVE_MINUTES
  FIFTEEN_MINUTES
  ONE_HOUR
  ONE_DAY
}

input ValidationFilters {
  status: ValidationStatus
  errorType: ErrorType
  intent: String
  minLatency: Int
  maxLatency: Int
}

enum ReportType {
  HIPAA_COMPLIANCE
  SOC2_COMPLIANCE
  ISO27001_COMPLIANCE
  QUALITY_SUMMARY
  ERROR_ANALYSIS
}
```

**Subscriptions** (Real-Time Updates):
```graphql
type Subscription {
  # Real-time metric updates
  validationMetricsUpdated(tenantId: ID!): ValidationMetrics!

  # New alert triggered
  alertTriggered(tenantId: ID!): Alert!

  # Validation completed
  validationCompleted(tenantId: ID!): ValidationDetail!
}
```

### Alerting System

**Alert Rules**:

**Configuration** (YAML):
```yaml
alert_rules:
  - name: "High Error Rate"
    severity: CRITICAL
    condition: "error_rate > 0.10"  # 10% error rate
    duration: "15m"  # Sustained for 15 minutes
    channels: [email, slack, pagerduty]
    message: "Validation error rate is {{value}}% (threshold: 10%). Check recent failed validations."

  - name: "Latency Spike"
    severity: HIGH
    condition: "p95_latency_ms > 800"  # P95 latency above 800ms
    duration: "10m"
    channels: [slack]
    message: "P95 validation latency is {{value}}ms (threshold: 800ms). Solver pool may be overloaded."

  - name: "Cache Hit Rate Drop"
    severity: MEDIUM
    condition: "cache_hit_rate < 0.50"  # Cache hit rate below 50%
    duration: "30m"
    channels: [email]
    message: "Cache hit rate is {{value}}% (threshold: 50%). Consider cache warming or TTL adjustment."

  - name: "HIPAA Violation Detected"
    severity: CRITICAL
    condition: "hipaa_violations > 0"
    duration: "1m"
    channels: [email, pagerduty]
    message: "HIPAA violation detected in conversation {{conversation_id}}. Immediate review required."
```

**Alert Channels**:

**Email**:
```python
def send_email_alert(alert):
    send_email(
        to=alert.recipients,
        subject=f"[{alert.severity}] {alert.name}",
        body=f"""
        Alert: {alert.name}
        Severity: {alert.severity}
        Triggered At: {alert.triggered_at}
        Message: {alert.message}

        View Details: https://dashboard.hapyy.ai/alerts/{alert.id}
        """
    )
```

**Slack**:
```python
def send_slack_alert(alert):
    slack_client.chat_postMessage(
        channel='#aidi-alerts',
        text=f"🚨 *{alert.severity}*: {alert.name}",
        blocks=[{
            "type": "section",
            "text": {"type": "mrkdwn", "text": alert.message}
        }, {
            "type": "actions",
            "elements": [{
                "type": "button",
                "text": {"type": "plain_text", "text": "View Details"},
                "url": f"https://dashboard.hapyy.ai/alerts/{alert.id}"
            }]
        }]
    )
```

**PagerDuty**:
```python
def send_pagerduty_alert(alert):
    pagerduty_client.trigger_incident(
        service_id=alert.pagerduty_service,
        incident_key=alert.id,
        summary=f"{alert.name}: {alert.message}",
        severity=alert.severity.lower(),
        custom_details={
            'tenant_id': alert.tenant_id,
            'alert_id': alert.id,
            'dashboard_url': f"https://dashboard.hapyy.ai/alerts/{alert.id}"
        }
    )
```

**Alert Deduplication**:
```python
def should_trigger_alert(alert_rule, current_value):
    """Prevent alert spam by deduplicating similar alerts"""
    # Check if similar alert already active
    existing_alert = get_active_alert(alert_rule.name, alert_rule.tenant_id)

    if existing_alert:
        # Update existing alert instead of creating new
        existing_alert.update(current_value=current_value)
        return False

    # No existing alert, create new
    return True
```

### Compliance Reporting

**Report Templates**:

**HIPAA Compliance Report** (monthly):
```markdown
# HIPAA Compliance Report - HealthCo Insurance
**Period**: January 2025
**Generated**: 2025-02-01

## Executive Summary
- Total Conversations Validated: 312,450
- HIPAA Violations Detected: 3 (0.001%)
- All violations remediated within 24 hours

## Validation Coverage
- Percentage of conversations validated: 99.8%
- Validation success rate: 96.2%

## HIPAA Violation Details
| Date | Conversation ID | Violation Type | Remediation |
|------|----------------|----------------|-------------|
| 2025-01-05 | conv_12345 | PHI disclosed without consent | Call flagged, not delivered to customer |
| 2025-01-18 | conv_67890 | Minimum necessary rule violated | Retrained chatbot to limit disclosures |
| 2025-01-24 | conv_24680 | Accessed records outside scope | Access controls updated |

## Recommendations
1. Review chatbot training data to prevent future PHI disclosure issues
2. Implement additional pre-validation filters for high-risk conversation types
3. Schedule quarterly HIPAA compliance training for chatbot developers

## Audit Trail
Full audit trail available at: https://dashboard.hapyy.ai/audit/2025-01

**Certified by**: [Automated System]
**Reviewed by**: [Compliance Officer Name]
```

**Report Generation**:
```python
def generate_compliance_report(tenant_id, report_type, start_date, end_date):
    """Generate compliance report and export to PDF"""
    # Query validation data
    validations = get_validations(tenant_id, start_date, end_date)

    # Calculate metrics
    total_validations = len(validations)
    violations = [v for v in validations if v.is_compliance_violation]
    success_rate = sum(1 for v in validations if v.status == 'VALID') / total_validations

    # Render report template
    report_content = render_template(
        f'{report_type}_template.md',
        tenant=get_tenant(tenant_id),
        period=f"{start_date} to {end_date}",
        total_validations=total_validations,
        violations=violations,
        success_rate=success_rate * 100
    )

    # Convert to PDF
    pdf_bytes = markdown_to_pdf(report_content)

    # Store and return
    report_id = save_report(tenant_id, report_type, pdf_bytes)

    return {
        'report_id': report_id,
        'download_url': f"https://api.hapyy.ai/reports/{report_id}/download",
        'preview_url': f"https://dashboard.hapyy.ai/reports/{report_id}"
    }
```

### Role-Based Access Control

**User Roles**:

| Role | Permissions | Use Case |
|------|-------------|----------|
| **System Admin** | All tenants, all operations | Hapyy internal operations |
| **Tenant Admin** | All operations for specific tenant | Client IT administrator |
| **Manager** | View dashboards, generate reports, configure alerts | Department manager |
| **Analyst** | View dashboards, export data | Data analyst, QA team |
| **Viewer** | Read-only dashboard access | Executive, stakeholder |

**Permission Matrix**:

| Feature | System Admin | Tenant Admin | Manager | Analyst | Viewer |
|---------|--------------|--------------|---------|---------|--------|
| View Dashboard | ✓ | ✓ | ✓ | ✓ | ✓ |
| Export Data | ✓ | ✓ | ✓ | ✓ | ✗ |
| Configure Alerts | ✓ | ✓ | ✓ | ✗ | ✗ |
| Manage Users | ✓ | ✓ | ✗ | ✗ | ✗ |
| Edit Knowledge Base | ✓ | ✓ | ✗ | ✗ | ✗ |
| Generate Reports | ✓ | ✓ | ✓ | ✓ | ✗ |
| Access Audit Log | ✓ | ✓ | ✓ | ✗ | ✗ |

**Implementation** (PostgreSQL + JWT):
```sql
CREATE TABLE user_roles (
    user_id UUID REFERENCES users(id),
    tenant_id UUID REFERENCES tenants(id),
    role VARCHAR(50) NOT NULL,
    PRIMARY KEY (user_id, tenant_id)
);

CREATE TABLE role_permissions (
    role VARCHAR(50) NOT NULL,
    permission VARCHAR(100) NOT NULL,
    PRIMARY KEY (role, permission)
);

-- Insert permissions
INSERT INTO role_permissions VALUES
    ('tenant_admin', 'dashboard:view'),
    ('tenant_admin', 'dashboard:export'),
    ('tenant_admin', 'alerts:configure'),
    ('tenant_admin', 'users:manage'),
    ('manager', 'dashboard:view'),
    ('manager', 'dashboard:export'),
    ('manager', 'alerts:configure'),
    ('analyst', 'dashboard:view'),
    ('analyst', 'dashboard:export'),
    ('viewer', 'dashboard:view');
```

**Authorization Check** (GraphQL resolver):
```javascript
const resolvers = {
  Query: {
    validationMetrics: async (parent, args, context) => {
      // Check authentication
      if (!context.user) {
        throw new AuthenticationError('Not authenticated');
      }

      // Check tenant access
      if (context.user.tenantId !== args.tenantId && !context.user.isSystemAdmin) {
        throw new ForbiddenError('Access denied to this tenant');
      }

      // Check permission
      if (!context.user.hasPermission('dashboard:view')) {
        throw new ForbiddenError('Permission denied');
      }

      // Fetch and return data
      return fetchValidationMetrics(args.tenantId, args.timeRange);
    }
  }
};
```

### White-Label Customization

**Configurable Branding**:
```json
{
  "tenant_id": "innova",
  "branding": {
    "product_name": "AIDI Quality Assurance",
    "logo_url": "https://innova.com/assets/logo.png",
    "favicon_url": "https://innova.com/assets/favicon.ico",
    "primary_color": "#1E40AF",
    "secondary_color": "#3B82F6",
    "custom_domain": "quality.aidi.innova.com",
    "support_email": "support@innova.com",
    "support_url": "https://support.innova.com"
  }
}
```

**Dynamic Theming** (React):
```javascript
const theme = createTheme({
  palette: {
    primary: {
      main: tenant.branding.primaryColor
    },
    secondary: {
      main: tenant.branding.secondaryColor
    }
  },
  typography: {
    fontFamily: tenant.branding.fontFamily || 'Roboto, sans-serif'
  }
});

function App() {
  return (
    <ThemeProvider theme={theme}>
      <Dashboard tenant={tenant} />
    </ThemeProvider>
  );
}
```

**Custom Domain Setup**:
```nginx
# NGINX configuration for white-label domain
server {
    listen 443 ssl;
    server_name quality.aidi.innova.com;

    ssl_certificate /etc/ssl/certs/innova.crt;
    ssl_certificate_key /etc/ssl/private/innova.key;

    location / {
        proxy_pass http://dashboard-app:3000;
        proxy_set_header Host $host;
        proxy_set_header X-Tenant-ID innova;
    }
}
```

### Export Capabilities

**CSV Export**:
```python
def export_csv(validations):
    """Export validations to CSV"""
    import csv
    from io import StringIO

    output = StringIO()
    writer = csv.DictWriter(output, fieldnames=[
        'validation_id', 'timestamp', 'status', 'intent',
        'latency_ms', 'error_type', 'explanation'
    ])

    writer.writeheader()
    for v in validations:
        writer.writerow({
            'validation_id': v.id,
            'timestamp': v.timestamp.isoformat(),
            'status': v.status,
            'intent': v.intent,
            'latency_ms': v.latency_ms,
            'error_type': v.error_type or '',
            'explanation': v.explanation or ''
        })

    return output.getvalue()
```

**PDF Export** (Dashboard snapshot):
```python
from weasyprint import HTML

def export_dashboard_pdf(tenant_id, dashboard_html):
    """Export dashboard as PDF"""
    pdf_bytes = HTML(string=dashboard_html).write_pdf()
    return pdf_bytes
```

**JSON Export**:
```python
def export_json(validations):
    """Export validations to JSON"""
    return json.dumps([{
        'validation_id': v.id,
        'timestamp': v.timestamp.isoformat(),
        'status': v.status,
        'conversation': {
            'user_query': v.user_query,
            'bot_response': v.bot_response
        },
        'validation_result': {
            'explanation': v.explanation,
            'counterexample': v.counterexample
        },
        'performance': {
            'latency_ms': v.latency_ms,
            'solver_time_ms': v.solver_time_ms
        }
    } for v in validations], indent=2)
```

## Performance & Scalability

**Query Optimization**:
- **Materialized Views**: Pre-aggregate common queries (daily/weekly success rates)
- **Caching**: Redis cache for frequently accessed dashboards (5-minute TTL)
- **Connection Pooling**: Database connection pools (100 connections per pod)
- **Query Batching**: DataLoader batches multiple GraphQL queries

**Horizontal Scaling**:
- Dashboard API: 4-16 pods (auto-scale based on CPU)
- GraphQL API: 4-16 pods (auto-scale based on request rate)
- Report Generator: 2-8 pods (queue-based, scale on queue depth)

**Performance Targets**:
- Dashboard load time: <2 seconds
- GraphQL query response: <500ms P95
- Real-time metric update: <15 seconds latency
- Report generation: <30 seconds for monthly report

## References

1. **Multi-Tenant SaaS Architecture**:
   - Chong, F., et al. (2006). "Multi-Tenant Data Architecture". Microsoft Architecture Journal.
   - "AWS SaaS Architecture Fundamentals". https://aws.amazon.com/saas/

2. **Real-Time Analytics**:
   - "Kafka Streams Documentation". https://kafka.apache.org/documentation/streams/
   - "InfluxDB Best Practices". https://docs.influxdata.com/influxdb/

3. **GraphQL**:
   - "GraphQL Specification". https://spec.graphql.org/
   - "Apollo Server Documentation". https://www.apollographql.com/docs/apollo-server/

4. **Compliance Reporting**:
   - "HIPAA Security Rule". U.S. Department of Health & Human Services.
   - "SOC 2 Trust Service Criteria". AICPA.

5. **Dashboard Design**:
   - Few, S. (2006). "Information Dashboard Design". O'Reilly Media.
   - "Material-UI Documentation". https://mui.com/