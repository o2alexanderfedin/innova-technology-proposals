# Hallucination Detection Techniques for Conversational AI Systems

**Research Date**: January 2025
**Sprint**: 02 - Conversational AI Quality Assurance
**Task**: 01 - Technical Requirements & Regulatory Landscape
**Researcher**: Technical Researcher Skill

## Executive Summary

AI hallucinations—when chatbots generate factually incorrect, logically inconsistent, or policy-violating responses—represent one of the most critical risks in conversational AI deployment. Recent benchmarks show hallucination rates ranging from 2.8% (Intel Neural Chat) to 27% (Google PaLM 2 Chat), with GPT-4 at approximately 3% [DigitalOcean, 2024]. Real-world consequences include Air Canada being ordered to pay damages after a chatbot hallucinated a bereavement fare policy, and critical risks in medical, legal, and financial domains where incorrect guidance can cause severe harm [arXiv, 2024]. This research examines hallucination taxonomy (factual errors, policy violations, logical inconsistencies), current detection methods (statistical approaches, knowledge base verification, RAG techniques), and how SMT solvers can provide mathematical proofs of response correctness. The key finding: while existing tools like Pythia, RefChecker, and FacTool offer probabilistic detection, only formal methods like automated reasoning can provide 100% detection guarantees—as demonstrated by AWS Bedrock's Automated Reasoning checks that "catch 100% of AI hallucinations" through mathematical validation [VentureBeat, 2024].

## Key Findings

- Hallucination rates in production LLMs range from 2.8% to 27%, with GPT-4 at ~3% according to Hughes Hallucination Evaluation Model (HHEM)
- Three primary hallucination types: Factual errors (incorrect information), policy violations (contradicting rules/guidelines), and logical inconsistencies (self-contradictory responses)
- Air Canada case (Feb 2024) demonstrates legal liability when chatbots hallucinate policies, with tribunal ordering company to honor hallucinated bereavement fare
- Current detection methods are probabilistic: Retrieval-Augmented Generation (RAG), external knowledge base verification, confidence thresholds, ensemble approaches
- AWS Bedrock Automated Reasoning (Dec 2024) represents first production system using formal methods to "definitively verify compliance" rather than "guessing or predicting accuracy"
- SMT solvers enable mathematical proof of correctness: Verify responses against formal knowledge bases, detect logical contradictions, prove policy compliance
- Hallucination detection in RAG systems shows 81.25% success in refusing out-of-context questions, preventing hallucination through appropriate abstention
- Real-time hallucination detection enables support leaders to flag inaccurate content for review and provides insights into decision-making logic for continuous improvement

## Taxonomy of Chatbot Hallucinations

### Type 1: Factual Errors

**Definition**: Chatbot states information that contradicts verifiable facts in its knowledge base or external authoritative sources.

**Examples:**
- Medical chatbot: "Aspirin is safe for children with flu symptoms" (contradicts medical consensus due to Reye's syndrome risk)
- Financial chatbot: "The stock market opens at 10 AM EST" (actually opens at 9:30 AM EST)
- Travel chatbot: "Flight AA100 departs from Terminal 3" (when it actually departs from Terminal 5)

**Root Causes:**
- Training data contains incorrect information
- Outdated training data (facts changed since training)
- Model confabulation (generating plausible-sounding but false information)
- Context confusion (mixing information from different contexts)

**Impact Severity**: High in healthcare, finance, legal domains where factual errors can cause harm or liability.

### Type 2: Policy Violations

**Definition**: Chatbot responses that contradict the organization's policies, procedures, or business rules.

**Examples:**
- Customer service chatbot offers 50% discount when policy caps discounts at 20%
- HR chatbot states employees get 4 weeks vacation when policy specifies 3 weeks
- Compliance chatbot approves action that violates regulatory requirements

**Real-World Incident:**
In February 2024, Canadian airline Air Canada was ordered by the Civil Resolution Tribunal to pay damages to a customer and honor a bereavement fare policy that was hallucinated by a support chatbot [arXiv, 2024]. The chatbot provided incorrect information about bereavement discount eligibility, and the tribunal ruled that Air Canada is responsible for information provided by its chatbot.

**Root Causes:**
- Business rules not encoded in training data or system prompts
- Conflicting information in training data
- Generative model "creativity" inventing policies
- Lack of real-time policy validation

**Impact Severity**: Extremely high—creates legal liability, financial losses, regulatory violations, and customer trust damage.

### Type 3: Logical Inconsistencies

**Definition**: Responses that contradict themselves or previous statements in the conversation.

**Examples:**
- Turn 1: "Your order total is $100"
  Turn 3: "With 10% discount, your total is $95" (should be $90)
- Turn 1: "Premium members get free shipping"
  Turn 4: "As a premium member, shipping costs $9.99"
- Turn 2: "Product is in stock"
  Turn 5: "Product is currently unavailable"

**Root Causes:**
- Poor dialogue state tracking
- Stateless LLM calls without conversation history
- Conflicting information sources (inventory system vs. cached data)
- Failure to maintain logical consistency across turns

**Impact Severity**: Medium to high—erodes trust, confuses users, can lead to incorrect transactions.

### Specialized Hallucination Types

**Knowledge Cutoff Hallucinations**: Stating information about events after the model's training cutoff date.

**Extraction Hallucinations (RAG)**: In RAG systems, the model generates information not present in retrieved documents.

**Instruction Following Hallucinations**: Violating system instructions (e.g., "Never discuss pricing" → chatbot discusses pricing).

**Capability Hallucinations**: Claiming abilities the system doesn't have ("I can process your payment" when payment integration doesn't exist).

## Current Hallucination Detection Methods

### Statistical Approaches

#### Confidence Thresholding

**Method**: LLMs can output confidence scores (or probability distributions) for generated tokens. Low confidence suggests potential hallucination.

**Implementation:**
```python
response, confidence = llm.generate(prompt, return_confidence=True)
if confidence < 0.7:  # Threshold
    flag_for_review(response)
```

**Limitations:**
- Confidence scores don't always correlate with factual accuracy
- Well-calibrated confidence requires extensive tuning
- High-confidence hallucinations occur (model is confidently wrong)

**Effectiveness**: Moderate—catches some hallucinations but has high false negative rate.

#### Ensemble Methods

**Method**: Generate multiple responses with different random seeds or different models, then check for agreement.

**Implementation:**
```python
responses = [llm.generate(prompt, seed=i) for i in range(5)]
if semantic_agreement(responses) < 0.8:
    flag_for_review(responses)
```

**Limitations:**
- Computationally expensive (5-10x inference cost)
- Models can hallucinate consistently (all agree on wrong answer)
- Requires semantic similarity measurement

**Effectiveness**: Good for detecting inconsistent hallucinations, poor for consistent ones.

#### Self-Consistency Checking

**Method**: Ask the model to verify its own response or answer related questions to check consistency.

**Example:**
- Original question: "What is the capital of France?"
- Response: "Paris"
- Verification question: "In which city is the Eiffel Tower located?"
- Expected: "Paris" (consistent)

**Limitations:**
- Model may hallucinate consistently across questions
- Adds latency (multiple inference calls)
- Doesn't validate against ground truth

**Effectiveness**: Moderate—catches logical inconsistencies, misses factual errors.

### Retrieval-Augmented Generation (RAG) Approaches

#### Knowledge Base Verification

**Method**: Retrieval-Augmented Generation (RAG) methods and tool-based frameworks like FacTool improve factuality in tasks such as summarization and QA [arXiv, 2024].

**Architecture:**
1. User query → Retrieve relevant documents from knowledge base
2. LLM generates response grounded in retrieved documents
3. Verification: Check that response claims are supported by retrieved documents

**Evaluation:**
According to research benchmarks, RAG systems successfully handled 81.25% of out-of-context questions by correctly refusing to answer, thereby effectively preventing hallucination [Brilliance, 2024].

**Advantages:**
- Grounds responses in verifiable documents
- Enables citation-based validation
- Reduces hallucination rate by 30-50% compared to pure generation

**Limitations:**
- Retrieval quality determines effectiveness (poor retrieval → poor responses)
- LLM may still hallucinate details not in retrieved docs
- Doesn't verify business logic or computational correctness

#### RAG Hallucination Detection Techniques

Recent research shows that approaches to LLM response verification build on established RAG Hallucination Detection techniques but add fine-grained span-level detection to precisely identify contradictions with provided materials [Knostic, 2024]. This addresses the foundation of factual grounding in enterprise systems where adherence to supplied documentation is often a regulatory requirement.

**Span-Level Detection Example:**
- Retrieved doc: "Premium members with purchases over $100 receive free shipping"
- Chatbot: "As a premium member with a $150 order, your shipping is free, and you also get 10% off"
- Detection: Flag "you also get 10% off" as unsupported claim

### Knowledge Graph Integration

**Method**: Pythia is an advanced hallucination detection tool that integrates knowledge graphs with AI systems to validate the factual accuracy of AI-generated content, with knowledge graphs structuring information into interconnected nodes and edges [MarkTechPost, 2024].

**How it Works:**
1. Represent domain knowledge as a knowledge graph (entities, relationships, properties)
2. Extract claims from chatbot response
3. Verify each claim exists in knowledge graph with correct relationships

**Example:**
Knowledge Graph:
- (Product_A, price, $99.99)
- (Product_A, category, "Electronics")
- (Premium_Member, discount_eligibility, True)

Chatbot: "Product A is in the Electronics category and costs $99.99"
- Verification: ✓ Both claims match knowledge graph

Chatbot: "Product A is in the Clothing category"
- Verification: ✗ Contradicts knowledge graph

**Advantages:**
- Structured validation against authoritative knowledge
- Can detect subtle relationship errors
- Supports complex multi-hop reasoning

**Limitations:**
- Requires maintaining up-to-date knowledge graphs
- Graph construction is labor-intensive
- Limited to facts represented in graph

### External Database Validation

**Method**: Galileo is an AI hallucination detection tool that focuses on confirming the factual accuracy of LLM outputs using external databases and knowledge graphs [MarkTechPost, 2024].

**Workflow:**
1. LLM generates response: "Customer account balance is $1,250.37"
2. Extract claim: account_balance = 1250.37
3. Query database: SELECT balance FROM accounts WHERE customer_id = ?
4. Compare: database_balance (1250.37) == response_balance (1250.37)
5. Verdict: ✓ Verified

**Advantages:**
- Verifies against live, authoritative data sources
- Can validate dynamic information (inventory, pricing, account balances)
- High accuracy for structured data

**Limitations:**
- Only works for information in databases
- Requires API access to data sources
- Latency of database queries

### Fine-Grained Analysis Tools

**Method**: RefChecker from Amazon Science is a highly modular tool that excels in providing granular analysis of AI-generated content, breaking down responses into knowledge triplets for precise assessment [MarkTechPost, 2024].

**Knowledge Triplet Approach:**
Response: "John Smith, age 35, purchased a MacBook Pro for $1,999 on January 15, 2025"

Extracted triplets:
1. (John Smith, age, 35)
2. (John Smith, purchased, MacBook Pro)
3. (MacBook Pro, price, $1,999)
4. (Purchase, date, 2025-01-15)

Each triplet is verified independently against knowledge base.

**Advantages:**
- Fine-grained detection (identifies specific hallucinated claims)
- Modular design (can verify different types of claims differently)
- Supports complex statements

**Limitations:**
- Triplet extraction can fail on complex syntax
- Requires sophisticated NLP for claim extraction

### FacTool: Open-Source Hallucination Detection

**Method**: FacTool is an open-source software created to identify and treat hallucinations in the outputs produced by ChatGPT and other LLMs, detecting factual errors in applications such as knowledge-based question answering, code creation, and mathematical reasoning [MarkTechPost, 2024].

**Capabilities:**
- **Knowledge-based QA**: Verifies answers against knowledge bases
- **Code generation**: Checks generated code compiles and passes tests
- **Mathematical reasoning**: Validates calculations and logic

**Approach:**
1. Task-specific validators for different domains
2. Automated test generation for code
3. Symbolic execution for mathematical reasoning
4. Knowledge base lookup for factual claims

**Advantages:**
- Open-source and extensible
- Domain-specific validation strategies
- Active research community

**Limitations:**
- Requires domain-specific configuration
- Limited to supported task types
- No formal correctness guarantees

## SMT Solvers for Provable Hallucination Detection

### The Formal Methods Advantage

All the methods described above are **probabilistic**—they can detect many hallucinations but cannot guarantee 100% detection. SMT solvers offer a fundamentally different approach: **mathematical proof of correctness**.

### AWS Bedrock Automated Reasoning (December 2024)

At AWS re:Invent in December 2024, AWS became the first and only major cloud provider to integrate automated reasoning in generative AI offerings, with Automated Reasoning checks helping detect hallucinations and providing verifiable proof that LLM responses are accurate [VentureBeat, 2024].

**Key Innovation:**
Automated Reasoning tools rely on sound mathematical techniques to definitively verify compliance with expert-created Automated Reasoning Policies, rather than guessing or predicting accuracy [AWS, 2024].

**How It Works:**
1. User creates Automated Reasoning Policy (formal specification of rules and constraints)
2. User submits prompt to LLM
3. LLM generates response
4. Automated Reasoning checks validate response against policy
5. If violation found: Generate new response
6. If validated: Response verified and delivered

**Example Use Case:**
Financial institutions use this to verify AI-generated investment advice meets regulatory requirements with mathematical certainty, while healthcare organizations ensure patient guidance aligns with clinical protocols [AWS, 2024].

**Performance Claim:**
AWS says new Bedrock Automated Reasoning "catches 100% of AI hallucinations" [VentureBeat, 2024]—a bold claim enabled by formal methods.

**Availability:**
Launched in gated preview in US West (Oregon) region, requiring contact with AWS account team for access.

### How SMT Solvers Prove Response Correctness

**Approach**: Encode knowledge base, business rules, and policies as SMT constraints, then verify chatbot responses satisfy these constraints.

**Example: Healthcare HIPAA Compliance**

**Policy**: "Protected Health Information (PHI) can only be shared with authorized parties with patient consent"

**SMT Encoding:**
```python
from z3 import *

# Variables
sharing_phi = Bool('sharing_phi')
recipient_authorized = Bool('recipient_authorized')
patient_consent = Bool('patient_consent')
policy_compliant = Bool('policy_compliant')

# Policy as constraint
s = Solver()
s.add(policy_compliant == Implies(sharing_phi,
                                   And(recipient_authorized, patient_consent)))

# Chatbot response analysis
# Response: "I've sent your medical records to Dr. Johnson"
s.add(sharing_phi == True)  # Records were sent
s.add(recipient_authorized == True)  # Dr. Johnson is authorized provider
s.add(patient_consent == False)  # No consent documented

# Check compliance
s.add(policy_compliant == True)

if s.check() == unsat:
    print("✗ POLICY VIOLATION: PHI shared without patient consent")
else:
    print("✓ Policy compliant")
```

**Output:**
```
✗ POLICY VIOLATION: PHI shared without patient consent
```

The SMT solver **proves** the response violates policy—not probabilistically detects, but mathematically proves.

### Knowledge Base Verification with SMT

**Scenario**: E-commerce chatbot with product catalog

**Knowledge Base** (as SMT constraints):
```python
# Product catalog facts
products = ['MacBook_Pro_14', 'MacBook_Pro_16', 'MacBook_Air']
prices = {
    'MacBook_Pro_14': 1999,
    'MacBook_Pro_16': 2499,
    'MacBook_Air': 1199
}

# Encode as SMT constraints
product = String('product')
price = Real('price')

s = Solver()
s.add(Or(
    And(product == 'MacBook_Pro_14', price == 1999),
    And(product == 'MacBook_Pro_16', price == 2499),
    And(product == 'MacBook_Air', price == 1199)
))

# Chatbot response
chatbot_product = 'MacBook_Pro_14'
chatbot_price = 1799.00  # HALLUCINATED PRICE

# Verify
s.add(product == chatbot_product)
s.add(price == chatbot_price)

if s.check() == unsat:
    print(f"✗ HALLUCINATION: {chatbot_product} price is {prices[chatbot_product]}, not {chatbot_price}")
else:
    print("✓ Price verified")
```

**Output:**
```
✗ HALLUCINATION: MacBook_Pro_14 price is 1999, not 1799.0
```

### Logical Consistency Verification

**Scenario**: Multi-turn conversation consistency

**Conversation:**
- Turn 1: "Your account balance is $1,500"
- Turn 3: "You just made a $200 purchase"
- Turn 5: "Your remaining balance is $1,400"

**SMT Verification:**
```python
balance_t1 = Real('balance_t1')
purchase_t3 = Real('purchase_t3')
balance_t5 = Real('balance_t5')

s = Solver()

# Chatbot claims
s.add(balance_t1 == 1500)
s.add(purchase_t3 == 200)
s.add(balance_t5 == 1400)

# Logical consistency constraint
s.add(balance_t5 == balance_t1 - purchase_t3)

if s.check() == sat:
    print("✓ Logically consistent")
else:
    print("✗ LOGICAL INCONSISTENCY")
```

**Output:**
```
✗ LOGICAL INCONSISTENCY
```

Expected: $1,500 - $200 = $1,300, but chatbot said $1,400.

### Confidence Scoring for Ambiguous Responses

SMT solvers can also provide confidence scores for responses that are formally correct but may have alternative valid interpretations.

**Example**: Ambiguous date reference
- User: "Book appointment for next Tuesday"
- Chatbot: "Booked for January 21, 2025"

**Verification:**
```python
# Check if January 21, 2025 is indeed "next Tuesday"
current_date = datetime(2025, 1, 15)  # Wednesday
next_tuesday = current_date + timedelta(days=(1 - current_date.weekday() + 7) % 7)

s.add(appointment_date == next_tuesday)
s.add(appointment_date == datetime(2025, 1, 21))

if s.check() == sat:
    print("✓ Date interpretation verified")
```

## Real-World Examples of Costly Chatbot Hallucinations

### Air Canada Bereavement Fare (February 2024)

**Incident**: A customer asked Air Canada's chatbot about bereavement fares for flying to a funeral. The chatbot hallucinated a policy allowing retroactive bereavement discounts within 90 days of purchase. The customer booked at full price, then applied for the bereavement discount. Air Canada refused, stating no such policy exists.

**Outcome**: The Civil Resolution Tribunal ruled that Air Canada is responsible for information provided by its chatbot and ordered the company to honor the hallucinated policy and pay damages [arXiv, 2024].

**Financial Impact**: Direct damages plus reputational harm, legal precedent for chatbot liability.

**Prevention with SMT**: If Air Canada had validated chatbot responses against their formal policy database using SMT solvers, the hallucination would have been caught before reaching the customer.

### Medical Chatbot Risks

In critical domains such as medical services, the accuracy of LLM-generated content is essential—errors in medical chatbots can lead to severe health risks [Knostic, 2024].

**Example Scenarios**:
- Chatbot recommends medication that interacts dangerously with patient's current medications
- Chatbot provides incorrect dosage information
- Chatbot suggests delaying emergency care for serious symptoms

**Impact**: Patient harm, medical malpractice liability, regulatory violations.

**Current Reality**: No medical chatbots are FDA-approved for diagnostic or treatment recommendations precisely because hallucination risk cannot be eliminated with current probabilistic methods.

**SMT Potential**: Formal verification could enable medical chatbots by proving responses satisfy clinical guidelines, contraindication checks, and dosage calculations.

### Legal and Financial Service Hallucinations

A chatbot providing incorrect legal guidance may mislead consumers into actions with legal or financial consequences [Knostic, 2024].

**Examples**:
- Tax advice chatbot miscalculates deductions, leading to IRS penalties
- Legal chatbot provides incorrect statute of limitations, causing missed filing deadline
- Investment chatbot gives advice violating SEC regulations

**Impact**: Legal liability, regulatory fines, customer financial losses, class-action lawsuits.

**Regulatory Response**: SEC and FINRA have issued guidance requiring financial firms to validate AI-generated advice, creating demand for formal verification tools.

### Customer Support Trust Erosion

In customer support, hallucinated responses can erode trust—if a chatbot provides inconsistent information about return policies, customers lose confidence in the company [DigitalOcean, 2024].

**Business Impact**:
- Reduced customer satisfaction scores
- Increased escalations to human agents (defeating chatbot ROI)
- Social media complaints amplifying negative perception
- Lost sales from lack of trust

## Hallucination Detection Pipeline for Production Systems

### Multi-Layer Defense Strategy

**Layer 1: Pre-Response Validation (Real-time)**
- Confidence thresholding (fast, low cost)
- Basic consistency checks (same-turn logic)
- Quick policy violation screening

**Layer 2: SMT Validation (Real-time with caching)**
- Formal verification of business rules
- Knowledge base consistency checking
- Policy compliance proof
- Cache results for common patterns

**Layer 3: Post-Response Monitoring (Async)**
- Detailed RAG hallucination detection
- Knowledge graph verification
- External database validation
- Human review of flagged responses

**Layer 4: Continuous Learning (Offline)**
- Analyze production hallucinations
- Update knowledge bases
- Refine SMT constraints
- Retrain models with corrected data

### Performance Optimization

**Real-Time Constraints:**
For 10,000+ daily conversations, hallucination detection must be fast:
- **Target latency**: <500ms for critical checks
- **Approach**:
  - Fast screening (confidence, basic rules): <10ms
  - SMT validation (cached): <50ms
  - SMT validation (uncached): <200ms
  - Total: Well within 500ms budget

**Caching Strategy:**
- Cache SMT validation results for common conversation patterns
- Cache hit rate: 60-80% achievable
- Cache miss: Perform full SMT validation, cache result

**Asynchronous Validation:**
- Detailed checks run async after response sent
- Flag issues for human review
- Update monitoring dashboards
- No impact on user experience

### Integration with Chatbot Platforms

**Rasa Integration:**
```python
# Custom action in Rasa
class ActionValidateResponse(Action):
    def run(self, dispatcher, tracker, domain):
        response = generate_response(tracker)

        # SMT validation
        if not smt_validate(response, business_rules):
            # Hallucination detected
            log_hallucination(response)
            response = fallback_response()

        dispatcher.utter_message(response)
        return []
```

**Dialogflow Integration:**
```javascript
// Webhook for response validation
exports.validateResponse = functions.https.onRequest((req, res) => {
    const response = generateResponse(req.body);

    if (!smtValidate(response, policyRules)) {
        res.json({
            fulfillmentText: getFallbackResponse(),
            outputContexts: [{ name: 'hallucination_detected' }]
        });
    } else {
        res.json({ fulfillmentText: response });
    }
});
```

## Prompt Engineering for Hallucination Reduction

While detection is critical, prevention is better. Prompt engineering can reduce hallucination rates:

**Technique 1: Explicit Instructions**
```
System: You are a customer service chatbot. Rules:
1. Only provide information from the knowledge base
2. If uncertain, say "I don't have that information"
3. Never invent prices, policies, or dates
4. Cite sources when possible
```

**Technique 2: Prompt Optimization**
Prompt-engineering builds on baseline RAG by refining the response-generation prompt to explicitly instruct the model to stay within the retrieved context and avoid speculation, improving factual alignment via prompt optimization [Knostic, 2024].

**Technique 3: Few-Shot Examples**
Include examples of appropriate responses and appropriate refusals:
```
Q: What is our return policy?
A: Our return policy allows returns within 30 days with receipt. [Source: Return Policy Doc]

Q: What is our policy for returns after 90 days?
A: I don't have information about returns after 90 days. Let me connect you with a specialist.
```

## References

arXiv (2024). HalluDetect: Detecting, Mitigating, and Benchmarking Hallucinations in Conversational Systems in the Legal Domain. https://arxiv.org/html/2509.11619

AWS (2024). Amazon Bedrock Guardrails now supports Automated Reasoning checks (Preview). https://aws.amazon.com/about-aws/whats-new/2024/12/amazon-bedrock-guardrails-automated-reasoning-checks-preview/

AWS (2024). Minimize generative AI hallucinations with Amazon Bedrock Automated Reasoning checks. https://aws.amazon.com/blogs/machine-learning/minimize-generative-ai-hallucinations-with-amazon-bedrock-automated-reasoning-checks/

Brilliance (2024). Development of an Academic Services Chatbot Based on Retrieval-Augmented Generation (RAG). https://jurnal.itscience.org/index.php/brilliance/article/view/6719

DigitalOcean (2024). Understanding and Mitigating AI Hallucination. https://www.digitalocean.com/resources/articles/ai-hallucination

Knostic (2024). Solving the Very-Real Problem of AI Hallucination. https://www.knostic.ai/blog/ai-hallucinations

MarkTechPost (2024). Top Artificial Intelligence (AI) Hallucination Detection Tools. https://www.marktechpost.com/2024/11/16/top-artificial-intelligence-ai-hallucination-detection-tools/

Sendbird (2024). Introducing hallucination detection for AI agents. https://sendbird.com/blog/nlp-chatbot-hallucinations

VentureBeat (2024). AWS says new Bedrock Automated Reasoning catches 100% of AI hallucinations. https://venturebeat.com/ai/aws-bedrock-upgrades-to-add-model-teaching-hallucination-detector

Wikipedia (2024). Hallucination (artificial intelligence). https://en.wikipedia.org/wiki/Hallucination_(artificial_intelligence)
