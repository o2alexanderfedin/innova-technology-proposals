---
description: Automatically discover strategic opportunities from company-client context
argument-hint: none
allowed-tools: Task, Read, Write, WebSearch, WebFetch
---

# Discover Opportunities

You are executing the `/discover-opportunities` command to automatically identify strategic opportunities.

## Purpose

Autonomously identify 5-10 strategic opportunity areas by analyzing company capabilities against client domain needs using AI-powered pattern matching and market research.

## Steps to Execute

### Step 1: Validate Context Files

Check context/company-profile.md exists and has >200 words.
Check context/client-info.md exists OR domain documents present.
If insufficient context, prompt user to populate files.

### Step 2: Identify Domain Documents

Search project root for domain documents (PDFs, markdown files).
List discovered documents for context enrichment.

### Step 3: Load Company Capabilities

Read context/company-profile.md.
Extract:
- Technical expertise areas
- Technology stack and tools
- Industry experience
- Certifications and capabilities
- Team strengths
- Competitive advantages

### Step 4: Load Client/Domain Context

Read context/client-info.md and any domain documents.
Extract:
- Strategic priorities
- Pain points and challenges
- Industry regulations
- Market trends
- Technology gaps
- Budget and timeline constraints

### Step 5: Invoke Opportunity Discovery Skill

Use Task tool to invoke opportunity-discovery skill with context:
- Company capabilities
- Client needs and domain
- All domain documents
- Project configuration

Discovery skill will:
- Analyze capability-need intersections
- Research market opportunities (WebSearch)
- Validate market sizing (WebFetch)
- Identify regulatory tailwinds
- Assess competitive landscape
- Calculate strategic fit scores
- Generate 5-10 opportunity definitions

### Step 6: Generate Sprint Definitions

For each discovered opportunity:
- Create sprint number (01-10)
- Generate sprint slug from name
- Write sprint description
- Customize research questions
- Assign priority (High/Medium/Low)

Populate config/sprint-config.yml with all sprints.

### Step 7: Create Discovery Report

Write reports/00-opportunity-discovery.md with:
- Analysis methodology
- Company capabilities summary
- Client domain analysis
- Discovered opportunities (ranked by strategic fit)
- Strategic fit analysis
- Recommended phasing
- Aggregate metrics
- Next steps

### Step 8: Display Discovery Summary

List all discovered opportunities with:
- Strategic fit scores
- Top 3 recommendations
- Aggregate market opportunity
- Execution recommendations

### Step 9: Prompt for Execution

Ask user:
```
Discovered N opportunities. Execute all?
Options:
1. Yes - Execute all: /execute-all
2. Customize - Review and edit config/sprint-config.yml first
3. Execute specific: /execute-sprint [num]
```

## Success Criteria

- Context files analyzed
- 5-10 opportunities discovered
- Strategic fit scores calculated
- Sprint definitions created
- Discovery report generated
- Clear next steps provided

## Error Handling

If context insufficient:
```
WARNING: Context is incomplete

Company profile: [word count] words (need >200)
Client info: [word count] words (need >200)

Discovery quality will be limited with insufficient context.

Recommendations:
1. Populate context/company-profile.md with detailed capabilities
2. Populate context/client-info.md with client needs and domain
3. Add domain documents (PDFs, markdown) to project root

Continue anyway? (yes/no)
```

If no opportunities found:
```
WARNING: No high-fit opportunities discovered

Possible reasons:
- Company capabilities don't align with client domain
- Market opportunities limited in this space
- Need more detailed context information

Recommendations:
1. Expand company capabilities description
2. Broaden client domain or industry focus
3. Review context for completeness and accuracy
```

## Expected Output

User receives discovery report with 5-10 ranked opportunities, strategic fit analysis, and clear execution guidance.
