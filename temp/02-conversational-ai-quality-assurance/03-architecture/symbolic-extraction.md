# Symbolic Extraction Engine Architecture

**Research Date**: January 2025
**Sprint**: 02 - Conversational AI Quality Assurance
**Task**: 03 - Solution Architecture Design
**Researcher**: Solution Architect Skill

## Executive Summary

The Symbolic Extraction Engine is the critical bridge between natural language conversations and mathematical validation, transforming unstructured chatbot responses into formal logical representations that SMT solvers can verify. This component represents the core intellectual property and technical differentiator of the Hapyy Conversational QA platform, combining state-of-the-art NLP (Natural Language Processing) with domain-specific logic formulation to achieve deterministic validation of probabilistic AI outputs.

The engine's business value is substantial: it enables automated validation at scale (10,000+ conversations/day) without human knowledge engineering for each conversation, adapts to domain-specific terminology and business logic, and provides explainable results (showing *why* a response is valid or invalid). For Innova's AIDI platform specifically, this means validating healthcare, insurance, and financial services conversations with industry-specific entity recognition (policy numbers, ICD-10 codes, monetary amounts) and business rule extraction (pricing formulas, eligibility criteria, coverage limits).

The architecture employs a four-stage pipeline: preprocessing (text normalization and tokenization), entity extraction (identifying structured data), intent classification (determining conversation goals), and logic formulation (generating SMT-LIB constraints). Each stage is optimized for accuracy, latency, and extensibility, with fine-tuned transformer models for domain adaptation and rule-based logic for deterministic constraint generation.

## Key Design Decisions

- **Hybrid NLP Approach**: Combine transformer models (BERT, RoBERTa) for entity extraction with rule-based parsing for logic formulation, balancing accuracy and determinism
- **Domain-Specific Fine-Tuning**: Train specialized models for healthcare, insurance, finance using client conversation data (with privacy preservation)
- **Multi-Stage Pipeline**: Separate preprocessing, entity extraction, intent classification, and logic formulation for modularity and debuggability
- **Confidence Scoring**: Attach confidence scores to extracted entities and intents for quality control and fallback strategies
- **Context-Aware Extraction**: Maintain conversation history and user profile context for accurate reference resolution (e.g., "it" → "Plan A")
- **Knowledge Base Integration**: Dynamically load domain schemas (entity types, business rules) from knowledge base to guide extraction
- **Incremental Processing**: Support streaming mode for real-time validation of multi-turn conversations
- **Explainable Extraction**: Generate human-readable explanations of extraction decisions for debugging and trust

## Symbolic Extraction Pipeline

### Architecture Overview

**Textual Pipeline Diagram**:

```
┌─────────────────────────────────────────────────────────────────┐
│                     INPUT: CONVERSATION DATA                     │
│  {                                                               │
│    user_query: "What's the premium for Plan A, $500 deductible, │
│                 age 45?",                                        │
│    bot_response: "The monthly premium is $347.",                │
│    context: {user_profile: {age: 45}, history: [...]}          │
│  }                                                               │
└────────────────────────────┬────────────────────────────────────┘
                             │
┌────────────────────────────▼────────────────────────────────────┐
│                   STAGE 1: PREPROCESSING                         │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Text Normalization                                       │  │
│  │  - Lowercase, remove extra spaces                        │  │
│  │  - Expand contractions ("what's" → "what is")            │  │
│  │  - Normalize currency ($347 → 347 USD)                   │  │
│  └────────────────────────────┬─────────────────────────────┘  │
│  ┌────────────────────────────▼─────────────────────────────┐  │
│  │ Tokenization (spaCy)                                     │  │
│  │  - Split into tokens with POS tags                       │  │
│  │  - Dependency parsing for grammar structure              │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│                 STAGE 2: ENTITY EXTRACTION                       │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Named Entity Recognition (spaCy + BERT)                  │  │
│  │  - Insurance plans: "Plan A"                             │  │
│  │  - Monetary amounts: "$500", "$347"                      │  │
│  │  - Ages: "45"                                            │  │
│  │  - Dates: "January 15, 2025"                             │  │
│  └────────────────────────────┬─────────────────────────────┘  │
│  ┌────────────────────────────▼─────────────────────────────┐  │
│  │ Custom Entity Extractors                                 │  │
│  │  - Policy numbers (regex: [A-Z]{3}\d{7})                │  │
│  │  - ICD-10 codes (regex: [A-Z]\d{2}\.\d{1,2})           │  │
│  │  - Deductibles (keyword: "deductible" + amount)         │  │
│  └────────────────────────────┬─────────────────────────────┘  │
│  ┌────────────────────────────▼─────────────────────────────┐  │
│  │ Entity Normalization                                     │  │
│  │  - "Plan A" → plan_id: "plan_a"                          │  │
│  │  - "$500 deductible" → deductible: 500                   │  │
│  │  - "age 45" → applicant_age: 45                          │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│              STAGE 3: INTENT CLASSIFICATION                      │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Intent Classifier (RoBERTa fine-tuned)                   │  │
│  │  Input: "What's the premium for Plan A..."              │  │
│  │  Output: intent = "pricing_query" (confidence: 0.98)     │  │
│  └────────────────────────────┬─────────────────────────────┘  │
│  ┌────────────────────────────▼─────────────────────────────┐  │
│  │ Business Operation Mapping                               │  │
│  │  "pricing_query" → validate_premium_calculation()        │  │
│  │  "eligibility_check" → validate_coverage_eligibility()   │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│               STAGE 4: LOGIC FORMULATION                         │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Load Business Rules from Knowledge Base                  │  │
│  │  - Pricing formula for Plan A                            │  │
│  │  - Deductible options: [500, 1000, 2500, 5000]          │  │
│  │  - Age factors: 18-25: 0, 26-35: 25, 36-45: 62...      │  │
│  └────────────────────────────┬─────────────────────────────┘  │
│  ┌────────────────────────────▼─────────────────────────────┐  │
│  │ Constraint Generation                                    │  │
│  │  (declare-const plan String)                             │  │
│  │  (declare-const deductible Int)                          │  │
│  │  (declare-const age Int)                                 │  │
│  │  (declare-const premium Int)                             │  │
│  │  (assert (= plan "plan_a"))                              │  │
│  │  (assert (= deductible 500))                             │  │
│  │  (assert (= age 45))                                     │  │
│  │  (assert (= premium 347))                                │  │
│  │  (assert (pricing_formula plan deductible age premium))  │  │
│  └────────────────────────────┬─────────────────────────────┘  │
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────▼────────────────────────────────┐
│             OUTPUT: SMT-LIB FORMULA + METADATA                   │
│  {                                                               │
│    formula: "(declare-const plan String) ...",                  │
│    entities: {plan: "plan_a", deductible: 500, age: 45, ...},  │
│    intent: "pricing_query",                                     │
│    confidence: 0.98,                                            │
│    extraction_time_ms: 127                                      │
│  }                                                               │
└─────────────────────────────────────────────────────────────────┘
```

### Pipeline Stages Detail

#### Stage 1: Preprocessing

**Purpose**: Normalize text and prepare for entity extraction

**Components**:

**1.1 Text Normalization**:
- **Lowercase**: Convert to lowercase for case-insensitive matching
- **Whitespace**: Remove extra spaces, tabs, newlines
- **Contractions**: Expand ("what's" → "what is", "I'm" → "I am")
- **Currency**: Normalize currency formats ("$347" → "347 USD", "€250" → "250 EUR")
- **Numbers**: Normalize number formats ("5,000" → "5000", "thirty" → "30")
- **Dates**: Normalize date formats ("Jan 15" → "2025-01-15", "1/15/25" → "2025-01-15")

**Example**:
```python
Input:  "What's the premium for Plan A with a $500 deductible?"
Output: "what is the premium for plan a with a 500 usd deductible?"
```

**Implementation** (Python + spaCy):
```python
import spacy
import re

nlp = spacy.load("en_core_web_sm")

def preprocess(text):
    # Expand contractions
    text = text.replace("what's", "what is").replace("I'm", "I am")

    # Normalize currency
    text = re.sub(r'\$(\d+)', r'\1 USD', text)

    # Normalize numbers
    text = re.sub(r'(\d+),(\d+)', r'\1\2', text)  # 5,000 → 5000

    # Lowercase
    text = text.lower()

    # Remove extra whitespace
    text = ' '.join(text.split())

    return text
```

**1.2 Tokenization**:
- **Tool**: spaCy 3.7+ with `en_core_web_sm` model
- **Output**: List of tokens with:
  - Token text
  - Part-of-speech (POS) tag (NOUN, VERB, ADJ, etc.)
  - Dependency tag (subject, object, modifier, etc.)
  - Lemma (base form: "premiums" → "premium")

**Example**:
```python
doc = nlp("what is the premium for plan a with a 500 usd deductible?")

for token in doc:
    print(f"{token.text:12} {token.pos_:6} {token.dep_:10} {token.lemma_}")

# Output:
# what         PRON   attr       what
# is           AUX    ROOT       be
# the          DET    det        the
# premium      NOUN   nsubj      premium
# for          ADP    prep       for
# plan         NOUN   pobj       plan
# a            DET    det        a
# with         ADP    prep       with
# a            DET    det        a
# 500          NUM    nummod     500
# usd          NOUN   compound   usd
# deductible   NOUN   pobj       deductible
```

**1.3 Dependency Parsing**:
- Identify grammatical relationships between tokens
- Extract subject-verb-object triples
- Identify modifiers and their targets

**Example**:
```python
# Extract relationships
for token in doc:
    if token.dep_ == 'nsubj':
        print(f"Subject: {token.text} of verb: {token.head.text}")
    if token.dep_ == 'pobj':
        print(f"Object: {token.text} of preposition: {token.head.text}")

# Output:
# Subject: premium of verb: is
# Object: plan of preposition: for
# Object: deductible of preposition: with
```

**Performance**: 20-40ms per conversation turn

#### Stage 2: Entity Extraction

**Purpose**: Identify and extract structured data from text

**2.1 Named Entity Recognition (NER)**:

**Base Model**: spaCy's pre-trained NER recognizing standard entities:
- PERSON: Names of people
- ORG: Organizations, companies
- GPE: Countries, cities, states
- MONEY: Monetary values
- DATE: Dates and time periods
- CARDINAL: Numerical values

**Custom NER Model**: Fine-tuned BERT for domain-specific entities

**Training Data** (example for insurance domain):
```json
[
  {
    "text": "I'd like a quote for Plan A with a $500 deductible.",
    "entities": [
      {"start": 24, "end": 30, "label": "INSURANCE_PLAN"},
      {"start": 38, "end": 42, "label": "MONEY"},
      {"start": 43, "end": 53, "label": "DEDUCTIBLE"}
    ]
  },
  // ... 10,000+ examples
]
```

**Fine-Tuning Process**:
1. Start with pre-trained BERT-base (110M parameters)
2. Add custom NER head for insurance entities
3. Train on 10,000+ annotated conversations
4. Validate on held-out 20% test set
5. Target accuracy: >95% F1 score

**Custom Entity Types** (insurance domain):
- INSURANCE_PLAN: "Plan A", "Bronze Plan", "PPO 500"
- DEDUCTIBLE: "$500 deductible", "1000 dollar deductible"
- PREMIUM: "$347 monthly premium", "annual premium of $4,164"
- COVERAGE_LIMIT: "annual maximum of $1 million", "$8,000 out-of-pocket max"
- POLICY_NUMBER: "ABC1234567", "POL-2025-001"
- CONDITION: "diabetes", "hypertension", "asthma"
- PROCEDURE: "MRI scan", "colonoscopy", "annual checkup"
- PROVIDER: "Dr. Smith", "Memorial Hospital", "Walgreens Pharmacy"

**2.2 Custom Entity Extractors**:

**Regex-Based Extraction** (for structured formats):
```python
import re

def extract_policy_number(text):
    """Policy number format: ABC1234567"""
    pattern = r'\b[A-Z]{3}\d{7}\b'
    matches = re.findall(pattern, text)
    return matches

def extract_icd10_code(text):
    """ICD-10 diagnosis code format: A12.34"""
    pattern = r'\b[A-Z]\d{2}\.\d{1,2}\b'
    matches = re.findall(pattern, text)
    return matches

def extract_phone_number(text):
    """Phone number formats: (555) 123-4567, 555-123-4567"""
    pattern = r'\(?\d{3}\)?[-.\s]?\d{3}[-.\s]?\d{4}'
    matches = re.findall(pattern, text)
    return matches
```

**Rule-Based Extraction** (for domain patterns):
```python
def extract_deductible(doc):
    """Extract deductible amount from dependency-parsed document"""
    for token in doc:
        if token.lemma_ == 'deductible':
            # Look for monetary amount modifying 'deductible'
            for child in token.children:
                if child.like_num or child.ent_type_ == 'MONEY':
                    return int(child.text.replace(',', '').replace('$', ''))
    return None

def extract_premium(doc):
    """Extract premium amount and frequency"""
    for token in doc:
        if token.lemma_ in ['premium', 'payment', 'cost']:
            amount = None
            frequency = 'monthly'  # default

            for child in token.children:
                if child.like_num or child.ent_type_ == 'MONEY':
                    amount = int(child.text.replace(',', '').replace('$', ''))
                if child.lemma_ in ['annual', 'yearly', 'year']:
                    frequency = 'annual'
                if child.lemma_ in ['monthly', 'month']:
                    frequency = 'monthly'

            if amount:
                return {'amount': amount, 'frequency': frequency}
    return None
```

**2.3 Entity Normalization**:

**Purpose**: Convert extracted entities to canonical forms for SMT validation

**Normalization Rules**:
```python
def normalize_plan_name(plan_text):
    """Normalize insurance plan names"""
    # "Plan A" → "plan_a"
    # "Bronze Plan" → "bronze_plan"
    # "PPO 500" → "ppo_500"
    return plan_text.lower().replace(' ', '_')

def normalize_monetary_amount(amount_text):
    """Convert monetary text to integer cents"""
    # "$347" → 34700 (cents)
    # "1,234.56 USD" → 123456
    amount = amount_text.replace('$', '').replace(',', '').replace(' USD', '')
    if '.' in amount:
        dollars, cents = amount.split('.')
        return int(dollars) * 100 + int(cents)
    else:
        return int(amount) * 100

def normalize_date(date_text):
    """Convert date text to ISO format"""
    # "January 15, 2025" → "2025-01-15"
    # "1/15/25" → "2025-01-15"
    from dateutil import parser
    return parser.parse(date_text).strftime('%Y-%m-%d')
```

**Entity Disambiguation**:

Handle ambiguous entity references using conversation context:
```python
def resolve_entity_reference(entity, context):
    """Resolve pronouns and references to previously mentioned entities"""
    if entity.lower() in ['it', 'that', 'this']:
        # Look for most recent INSURANCE_PLAN in context
        for msg in reversed(context['conversation_history']):
            for ent in msg['entities']:
                if ent['type'] == 'INSURANCE_PLAN':
                    return ent['value']
    return entity
```

**Example**:
```
User: "Tell me about Plan A."
Bot: "Plan A is our bronze-level plan with a $500 deductible."
User: "What's the premium for it?"  # "it" → "Plan A"
Bot: "The monthly premium is $347."
```

**Performance**: 80-150ms per conversation turn

#### Stage 3: Intent Classification

**Purpose**: Determine the conversation goal and business operation

**Model Architecture**: RoBERTa fine-tuned for intent classification

**Base Model**: `roberta-base` (125M parameters)

**Fine-Tuning**:
- Training data: 20,000+ labeled conversations
- Classes: 15-20 intents per domain
- Optimizer: AdamW with learning rate 2e-5
- Batch size: 16
- Epochs: 3-5
- Validation: 80/20 train/val split
- Target accuracy: >95%

**Intent Taxonomy** (insurance domain):

**Primary Intents**:
- `pricing_query`: "What's the premium for Plan A?"
- `eligibility_check`: "Am I eligible for coverage with diabetes?"
- `coverage_inquiry`: "Does Plan A cover MRI scans?"
- `claim_status`: "What's the status of my claim ABC1234567?"
- `enrollment`: "I'd like to enroll in Plan A."
- `cancellation`: "I want to cancel my policy."
- `provider_search`: "Is Dr. Smith in-network?"
- `benefit_explanation`: "What's the difference between Plan A and Plan B?"

**Secondary Intents**:
- `greeting`: "Hello", "Hi there"
- `farewell`: "Thank you, goodbye"
- `clarification`: "Can you explain that again?"
- `complaint`: "I'm unhappy with my service"
- `escalation`: "I'd like to speak to a supervisor"

**Implementation**:
```python
from transformers import RobertaForSequenceClassification, RobertaTokenizer
import torch

class IntentClassifier:
    def __init__(self, model_path='models/insurance_intent_classifier'):
        self.tokenizer = RobertaTokenizer.from_pretrained('roberta-base')
        self.model = RobertaForSequenceClassification.from_pretrained(model_path)
        self.model.eval()

        self.intents = [
            'pricing_query', 'eligibility_check', 'coverage_inquiry',
            'claim_status', 'enrollment', 'cancellation',
            'provider_search', 'benefit_explanation'
        ]

    def classify(self, text):
        """Classify user query into intent"""
        inputs = self.tokenizer(text, return_tensors='pt', truncation=True, max_length=512)

        with torch.no_grad():
            outputs = self.model(**inputs)
            logits = outputs.logits
            probabilities = torch.softmax(logits, dim=1)

        predicted_class = torch.argmax(probabilities, dim=1).item()
        confidence = probabilities[0][predicted_class].item()

        return {
            'intent': self.intents[predicted_class],
            'confidence': confidence,
            'probabilities': {intent: prob for intent, prob in zip(self.intents, probabilities[0].tolist())}
        }
```

**Usage**:
```python
classifier = IntentClassifier()

result = classifier.classify("What's the monthly premium for Plan A with $500 deductible for age 45?")
print(result)

# Output:
# {
#   'intent': 'pricing_query',
#   'confidence': 0.982,
#   'probabilities': {
#     'pricing_query': 0.982,
#     'benefit_explanation': 0.012,
#     'eligibility_check': 0.004,
#     ...
#   }
# }
```

**Business Operation Mapping**:

Map intents to validation functions:
```python
INTENT_TO_VALIDATION = {
    'pricing_query': validate_premium_calculation,
    'eligibility_check': validate_coverage_eligibility,
    'coverage_inquiry': validate_coverage_statement,
    'claim_status': validate_claim_status,
    'benefit_explanation': validate_benefit_comparison,
}

def get_validation_function(intent):
    return INTENT_TO_VALIDATION.get(intent, validate_generic_response)
```

**Performance**: 40-80ms per conversation turn (GPU), 150-250ms (CPU)

#### Stage 4: Logic Formulation

**Purpose**: Generate SMT-LIB constraints from extracted entities and business rules

**4.1 Knowledge Base Schema Loading**:

Load domain-specific business rules for the identified intent:
```python
def load_business_rules(client_id, intent):
    """Load business rules from knowledge base"""
    kb = KnowledgeBase(client_id)

    if intent == 'pricing_query':
        return {
            'pricing_formula': kb.get_pricing_formula(),
            'deductible_options': kb.get_deductible_options(),
            'age_factors': kb.get_age_factors(),
            'state_multipliers': kb.get_state_multipliers(),
        }
    elif intent == 'eligibility_check':
        return {
            'age_limits': kb.get_age_limits(),
            'excluded_conditions': kb.get_excluded_conditions(),
            'residency_requirements': kb.get_residency_requirements(),
        }
    # ... other intents
```

**Example Knowledge Base Data** (pricing rules):
```json
{
  "pricing_formula": {
    "base_rate": 285,
    "age_factors": [
      {"min_age": 18, "max_age": 25, "factor": 0},
      {"min_age": 26, "max_age": 35, "factor": 25},
      {"min_age": 36, "max_age": 45, "factor": 62},
      {"min_age": 46, "max_age": 55, "factor": 120},
      {"min_age": 56, "max_age": 65, "factor": 180}
    ],
    "deductible_discounts": [
      {"deductible": 500, "discount": 0},
      {"deductible": 1000, "discount": -15},
      {"deductible": 2500, "discount": -35},
      {"deductible": 5000, "discount": -60}
    ],
    "state_multipliers": {
      "CA": 1.15,
      "NY": 1.25,
      "TX": 0.95
    }
  }
}
```

**4.2 Constraint Generation**:

**Template-Based Generation**:

Each intent has a constraint template that fills in extracted entities:

**Pricing Query Template**:
```python
def generate_pricing_constraints(entities, business_rules):
    """Generate SMT-LIB constraints for premium validation"""
    plan = entities.get('plan')
    deductible = entities.get('deductible')
    age = entities.get('age') or entities.get('applicant_age')
    stated_premium = entities.get('premium')

    # Retrieve pricing rules
    base_rate = business_rules['pricing_formula']['base_rate']
    age_factor = get_age_factor(age, business_rules['pricing_formula']['age_factors'])
    deductible_discount = get_deductible_discount(deductible, business_rules['pricing_formula']['deductible_discounts'])

    # Generate SMT-LIB formula
    formula = f"""
    (declare-const plan String)
    (declare-const deductible Int)
    (declare-const age Int)
    (declare-const stated_premium Int)
    (declare-const calculated_premium Int)

    ; Extracted values from conversation
    (assert (= plan "{plan}"))
    (assert (= deductible {deductible}))
    (assert (= age {age}))
    (assert (= stated_premium {stated_premium}))

    ; Pricing formula: base_rate + age_factor + deductible_discount
    (assert (= calculated_premium (+ {base_rate} {age_factor} {deductible_discount})))

    ; Validation: stated premium must equal calculated premium
    (assert (= stated_premium calculated_premium))

    (check-sat)
    (get-model)
    """

    return formula
```

**Eligibility Check Template**:
```python
def generate_eligibility_constraints(entities, business_rules):
    """Generate SMT-LIB constraints for eligibility validation"""
    age = entities.get('age')
    condition = entities.get('condition')
    state = entities.get('state')
    bot_decision = entities.get('eligibility_decision')  # "eligible" or "not_eligible"

    # Retrieve eligibility rules
    min_age = business_rules['age_limits']['min_age']
    max_age = business_rules['age_limits']['max_age']
    excluded_conditions = business_rules['excluded_conditions']

    # Generate SMT-LIB formula
    formula = f"""
    (declare-const age Int)
    (declare-const condition String)
    (declare-const is_eligible Bool)

    ; Extracted values
    (assert (= age {age}))
    (assert (= condition "{condition}"))

    ; Eligibility rules
    (assert (and (>= age {min_age}) (<= age {max_age})))  ; Age in range
    (assert (not (member condition {excluded_conditions})))  ; Condition not excluded

    ; Validation: bot decision matches calculated eligibility
    (assert (= is_eligible {bot_decision == 'eligible'}))

    (check-sat)
    (get-model)
    """

    return formula
```

**4.3 Formula Optimization**:

Simplify formulas before sending to SMT solver:
```python
def optimize_formula(formula):
    """Apply algebraic simplifications to SMT formula"""
    # Constant folding: (+ 285 62 0) → 347
    # Dead code elimination: Remove unused variables
    # Constraint propagation: If (= x 5) and (= y x), then (= y 5)

    # Example: Use Z3's simplify
    from z3 import parse_smt2_string, simplify

    constraints = parse_smt2_string(formula)
    simplified = simplify(constraints)

    return simplified.sexpr()
```

**Performance**: 50-100ms per conversation turn

### Context Management

**Purpose**: Maintain conversation state for reference resolution and entity tracking

**Context Structure**:
```python
class ConversationContext:
    def __init__(self):
        self.conversation_id = generate_uuid()
        self.history = []  # List of (role, content, entities, intent)
        self.entities = {}  # Accumulated entities across turns
        self.user_profile = {}  # Persistent user data
        self.session_data = {}  # Temporary session variables

    def add_turn(self, role, content, entities, intent):
        """Add conversation turn to history"""
        self.history.append({
            'role': role,
            'content': content,
            'entities': entities,
            'intent': intent,
            'timestamp': datetime.now()
        })

        # Accumulate entities
        for entity_type, entity_value in entities.items():
            self.entities[entity_type] = entity_value

    def get_entity(self, entity_type):
        """Retrieve entity from current turn or history"""
        return self.entities.get(entity_type)

    def resolve_reference(self, pronoun):
        """Resolve pronoun to previously mentioned entity"""
        # Look back through history for most recent entity of expected type
        for turn in reversed(self.history):
            if pronoun in ['it', 'that', 'this']:
                # Assume refers to most recent INSURANCE_PLAN
                if 'plan' in turn['entities']:
                    return turn['entities']['plan']
        return None
```

**Reference Resolution Example**:
```python
context = ConversationContext()

# Turn 1
context.add_turn('user', 'Tell me about Plan A', {'plan': 'plan_a'}, 'benefit_explanation')
context.add_turn('assistant', 'Plan A is our bronze-level plan...', {}, None)

# Turn 2
context.add_turn('user', 'What's the premium for it?', {}, 'pricing_query')

# Resolve "it" → "plan_a"
plan = context.resolve_reference('it')  # Returns 'plan_a'
```

**Entity Carryover**:

Entities mentioned earlier in the conversation are automatically available:
```python
# Turn 1: User provides age
context.add_turn('user', 'I'm 45 years old', {'age': 45}, 'user_info')

# Turn 2: Age not mentioned, but retrieved from context
context.add_turn('user', 'What's the premium for Plan A?', {'plan': 'plan_a'}, 'pricing_query')

# When generating constraints, retrieve age from context
age = context.get_entity('age')  # Returns 45
```

## Domain-Specific Fine-Tuning

### Training Data Collection

**Data Sources**:
1. **Client Conversation Logs**: Historical conversations from AIDI platform (with client permission)
2. **Synthetic Data Generation**: Create synthetic conversations using business rules
3. **Public Datasets**: Insurance Q&A datasets, financial services FAQs
4. **Manual Annotation**: Human labelers annotate entities and intents

**Privacy Preservation**:
- **De-identification**: Remove PII (names, SSNs, addresses) before training
- **Differential Privacy**: Add noise to training data to prevent memorization
- **Federated Learning**: Train on client data without centralizing (future)

### Entity Recognition Fine-Tuning

**Training Process**:

1. **Collect Annotations**:
   ```json
   [
     {
       "text": "I'd like a quote for Plan A with a $500 deductible.",
       "entities": [
         {"start": 24, "end": 30, "label": "INSURANCE_PLAN"},
         {"start": 38, "end": 42, "label": "MONEY"},
         {"start": 43, "end": 53, "label": "DEDUCTIBLE"}
       ]
     },
     // ... 10,000+ examples
   ]
   ```

2. **Convert to Training Format** (BIO tagging):
   ```
   I       O
   'd      O
   like    O
   a       O
   quote   O
   for     O
   Plan    B-INSURANCE_PLAN
   A       I-INSURANCE_PLAN
   with    O
   a       O
   $       B-MONEY
   500     I-MONEY
   deductible B-DEDUCTIBLE
   .       O
   ```

3. **Fine-Tune BERT Model**:
   ```python
   from transformers import BertForTokenClassification, Trainer, TrainingArguments

   model = BertForTokenClassification.from_pretrained(
       'bert-base-uncased',
       num_labels=len(entity_labels)
   )

   training_args = TrainingArguments(
       output_dir='./models/insurance_ner',
       num_train_epochs=5,
       per_device_train_batch_size=16,
       learning_rate=2e-5,
       evaluation_strategy='epoch',
   )

   trainer = Trainer(
       model=model,
       args=training_args,
       train_dataset=train_dataset,
       eval_dataset=val_dataset,
   )

   trainer.train()
   ```

4. **Evaluate**:
   ```python
   from seqeval.metrics import classification_report

   predictions = trainer.predict(test_dataset)
   print(classification_report(true_labels, predicted_labels))

   # Target Metrics:
   #                      precision    recall  f1-score   support
   # INSURANCE_PLAN         0.96      0.94      0.95       500
   # DEDUCTIBLE             0.98      0.97      0.98       400
   # PREMIUM                0.95      0.96      0.96       450
   # ...
   # Overall Accuracy: 0.96
   ```

### Intent Classification Fine-Tuning

**Training Process**:

1. **Collect Labeled Conversations**:
   ```csv
   text,intent
   "What's the premium for Plan A?",pricing_query
   "Am I eligible for coverage?",eligibility_check
   "Does this plan cover MRI scans?",coverage_inquiry
   ...
   ```

2. **Fine-Tune RoBERTa**:
   ```python
   from transformers import RobertaForSequenceClassification, Trainer

   model = RobertaForSequenceClassification.from_pretrained(
       'roberta-base',
       num_labels=len(intent_classes)
   )

   training_args = TrainingArguments(
       output_dir='./models/insurance_intent_classifier',
       num_train_epochs=3,
       per_device_train_batch_size=16,
       learning_rate=2e-5,
   )

   trainer = Trainer(model=model, args=training_args, train_dataset=train_dataset)
   trainer.train()
   ```

3. **Evaluate**:
   ```python
   from sklearn.metrics import classification_report

   predictions = trainer.predict(test_dataset)
   print(classification_report(true_labels, predicted_labels))

   # Target Accuracy: 95%+
   ```

## Error Handling and Edge Cases

### Low-Confidence Extractions

**Strategy**: If entity extraction or intent classification confidence < 0.8, flag for review

```python
if result['confidence'] < 0.8:
    return {
        'status': 'UNCERTAIN',
        'entities': result['entities'],
        'confidence': result['confidence'],
        'suggestion': 'Manual review recommended - low extraction confidence'
    }
```

### Missing Entities

**Strategy**: Use conversation context to infer missing entities

```python
def handle_missing_entity(entity_type, context):
    """Attempt to infer missing entity from context"""
    # Check conversation history
    entity_value = context.get_entity(entity_type)

    if entity_value:
        return entity_value

    # Check user profile
    if entity_type == 'age' and 'age' in context.user_profile:
        return context.user_profile['age']

    # Unable to infer - return None and flag
    return None
```

### Ambiguous Entities

**Example**: "I'm looking for coverage for my spouse."
- Is the pricing query for the user or the spouse?
- Age refers to user's age or spouse's age?

**Strategy**: Explicit disambiguation via conversation

```python
if entities.get('coverage_for') == 'spouse' and not entities.get('spouse_age'):
    return {
        'status': 'NEEDS_CLARIFICATION',
        'missing_info': ['spouse_age'],
        'suggestion': 'Ask: "What is your spouse\'s age?"'
    }
```

### Extraction Failures

**Fallback Strategy**:
1. **Attempt Basic Extraction**: Use regex and keyword matching
2. **Request Clarification**: Generate clarifying question for bot to ask user
3. **Skip Validation**: If extraction impossible, mark as UNKNOWN and log

## Performance Optimization

### Model Optimization

**1. Model Quantization**:
- **Technique**: Reduce model precision from FP32 to INT8
- **Tool**: ONNX Runtime, TensorRT
- **Benefit**: 4x faster inference, 75% memory reduction
- **Trade-off**: <1% accuracy loss

**2. Model Pruning**:
- **Technique**: Remove least important weights
- **Benefit**: 50% model size reduction, 2x faster
- **Trade-off**: 2-3% accuracy loss

**3. Knowledge Distillation**:
- **Technique**: Train smaller model (DistilBERT, 66M params) to mimic larger model (BERT, 110M params)
- **Benefit**: 60% faster, 40% smaller
- **Trade-off**: 3-5% accuracy loss

**Deployment Strategy**:
- **GPU Deployment**: Use full BERT/RoBERTa models for maximum accuracy
- **CPU Deployment**: Use DistilBERT or quantized models for cost efficiency

### Caching

**Entity Extraction Cache**:
- Cache entity extraction results for identical text
- Cache key: SHA256 hash of preprocessed text
- TTL: 1 hour (entities unlikely to change)
- Expected hit rate: 40-60% (many conversations have repeated patterns)

**Intent Classification Cache**:
- Cache intent classification for identical queries
- Expected hit rate: 30-50%

### Batching

**Batch Processing**:
- Process multiple conversations in parallel
- GPU utilization: Batch size 8-16 for optimal throughput
- Latency trade-off: Add 20-50ms batching delay for 5-10x throughput improvement

## Observability and Debugging

### Extraction Metrics

**Track**:
- Entity extraction rate (% of conversations with all required entities extracted)
- Intent classification accuracy (based on manual review sampling)
- Confidence score distribution
- Extraction latency (P50, P95, P99)

**Alerting**:
- Alert if entity extraction rate drops below 90%
- Alert if average confidence score drops below 0.85
- Alert if extraction latency P95 exceeds 200ms

### Explainability

**Extraction Report**:
```json
{
  "conversation_id": "conv_123",
  "extraction_report": {
    "entities_extracted": {
      "plan": {"value": "plan_a", "confidence": 0.98, "source": "NER"},
      "deductible": {"value": 500, "confidence": 0.95, "source": "regex"},
      "age": {"value": 45, "confidence": 1.0, "source": "context"}
    },
    "intent": {
      "value": "pricing_query",
      "confidence": 0.97,
      "top_3_intents": [
        {"intent": "pricing_query", "confidence": 0.97},
        {"intent": "benefit_explanation", "confidence": 0.02},
        {"intent": "coverage_inquiry", "confidence": 0.01}
      ]
    },
    "formula_generated": "(declare-const plan String) ...",
    "extraction_time_ms": 127
  }
}
```

## References

1. **Natural Language Processing**:
   - Devlin, J., et al. (2019). "BERT: Pre-training of Deep Bidirectional Transformers for Language Understanding". NAACL.
   - Liu, Y., et al. (2019). "RoBERTa: A Robustly Optimized BERT Pretraining Approach". arXiv.

2. **Named Entity Recognition**:
   - Lample, G., et al. (2016). "Neural Architectures for Named Entity Recognition". NAACL.
   - "spaCy Documentation". https://spacy.io/usage/linguistic-features#named-entities

3. **Intent Classification**:
   - Zhang, X., et al. (2015). "Character-level Convolutional Networks for Text Classification". NIPS.
   - Casanueva, I., et al. (2020). "Efficient Intent Detection with Dual Sentence Encoders". ACL.

4. **Symbolic AI**:
   - Russell, S., & Norvig, P. (2020). "Artificial Intelligence: A Modern Approach, 4th Edition". Pearson.
   - "SMT-LIB: The Satisfiability Modulo Theories Library". http://smtlib.cs.uiowa.edu/

5. **Model Optimization**:
   - "ONNX Runtime Performance Tuning". https://onnxruntime.ai/docs/performance/
   - Hinton, G., et al. (2015). "Distilling the Knowledge in a Neural Network". NeurIPS.

6. **Domain Adaptation**:
   - Howard, J., & Ruder, S. (2018). "Universal Language Model Fine-tuning for Text Classification". ACL.
   - "Hugging Face Transformers Documentation". https://huggingface.co/docs/transformers/

7. **Conversational AI**:
   - Gao, J., et al. (2019). "Neural Approaches to Conversational AI". Foundations and Trends in Information Retrieval.
   - Rasa, "NLU Training Data Format". https://rasa.com/docs/rasa/training-data-format/