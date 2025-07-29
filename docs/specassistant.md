# AI Spec-Assistant

The AI Spec-Assistant is an intelligent tool that helps improve specification quality by analyzing draft PRs and providing automated suggestions for requirements, proofs, and validation tests.

## Overview

The AI Spec-Assistant uses OpenAI's GPT-4 model with function-calling capabilities to:

- **Analyze PR diffs** for specification files (`.md`, `spec.yaml`)
- **Propose new requirements** using proper REQ/NFR format
- **Generate Lean proof skeletons** for formal verification
- **Create validation tests** for requirements
- **Validate specification language** for compliance

## How It Works

### Triggering the Assistant

The AI Spec-Assistant is triggered when:

1. A PR is opened or updated with markdown files
2. The PR has the `needs-spec-review` label
3. Files in the PR match specification patterns

### Analysis Process

1. **Diff Extraction**: Extracts changed markdown files from the PR
2. **Language Validation**: Checks for prohibited words and proper format
3. **Requirement Analysis**: Identifies missing requirements and suggests new ones
4. **Proof Generation**: Creates Lean proof skeletons for requirements
5. **Test Creation**: Generates validation tests for requirements
6. **Comment Posting**: Posts formatted suggestions as PR comments

## Usage

### Adding the Label

To trigger the AI Spec-Assistant on your PR:

```bash
# Add the label to your PR
gh pr edit <PR_NUMBER> --add-label "needs-spec-review"
```

### Example PR Structure

```markdown
# My Agent Specification

## Requirements

REQ 1: The agent MUST authenticate users before processing requests.
REQ 2: The agent SHOULD log all actions for audit purposes.

## Non-Functional Requirements

NFR 1: Response time MUST be under 100ms for 95% of requests.
NFR 2: The system MUST handle 1000 concurrent users.

## Traceability

REQ 1 → NFR 1: Authentication affects response time
REQ 2 → NFR 2: Logging impacts system capacity
```

### Expected AI Suggestions

The assistant might suggest:

```markdown
## AI Spec-Assistant Suggestions 🤖

### Requirement Suggestions

**REQ 3: The agent MUST validate input data before processing**
_Reasoning: Missing input validation requirement for security_
_Confidence: 85%_

**NFR 3: The system MUST encrypt sensitive data in transit**
_Reasoning: Security requirement for data protection_
_Confidence: 90%_

### Proof Suggestions

**Lean skeleton for REQ 1 authentication theorem**
_Reasoning: Formal proof needed for authentication requirement_
_Confidence: 80%_

### Test Suggestions

**Validation tests: 5 test cases for authentication**
_Reasoning: Comprehensive testing needed for security requirement_
_Confidence: 70%_
```

## Configuration

### Environment Variables

```bash
# Required for OpenAI API access
OPENAI_API_KEY=your_openai_api_key_here
```

### Prohibited Words

The assistant checks for these prohibited words in specifications:

- `MUSTN'T`
- `SHAN'T`
- `WON'T`
- `CANNOT`
- `IMPOSSIBLE`

### Allowed Words

These words are allowed in specifications:

- `MUST`
- `SHALL`
- `REQUIRED`
- `SHOULD`
- `RECOMMENDED`
- `MAY`
- `OPTIONAL`

## Validation Rules

### Specification Language

1. **REQ/NFR Format**: Requirements must use proper numbering
2. **Traceability**: Requirements should have traceability arrows (→)
3. **Prohibited Words**: No negative imperative words allowed
4. **Lean Integration**: Specifications should include formal proofs

### Lean Proof Requirements

1. **Theorem Names**: Must be descriptive and follow naming conventions
2. **Formal Statements**: Must be mathematically precise
3. **Proof Structure**: Must include clear proof steps
4. **Imports**: Must include necessary Lean libraries

### Test Requirements

1. **Unit Tests**: Individual requirement validation
2. **Integration Tests**: End-to-end requirement validation
3. **Property Tests**: Property-based testing for requirements
4. **Edge Cases**: Boundary condition testing

## Metrics and Monitoring

### Weekly Metrics

The assistant tracks weekly performance metrics:

- **Total Suggestions**: Number of suggestions generated
- **Accepted Suggestions**: Number of suggestions accepted by reviewers
- **Acceptance Rate**: Percentage of accepted suggestions (target: ≥60%)
- **Response Time**: Time to generate suggestions

### Metrics Dashboard

Weekly metrics are available in the GitHub Actions artifacts:

```bash
# Download weekly metrics report
gh run download --name ai-spec-metrics
```

## Integration with CI/CD

### Automated Checks

The assistant integrates with the CI/CD pipeline:

1. **Language Validation**: Checks for prohibited words
2. **Specification Linting**: Runs spectral linting on spec files
3. **Traceability Verification**: Ensures proper requirement mapping
4. **Lean Skeleton Validation**: Verifies proof structure

### Failure Conditions

The workflow fails if:

- Prohibited words are found in specifications
- Specification linting fails
- Traceability mappings are invalid
- Lean proof skeletons are missing required elements

## Best Practices

### Writing Good Specifications

1. **Use Clear Language**: Write requirements in simple, clear terms
2. **Include Rationale**: Explain why each requirement is needed
3. **Add Traceability**: Show how requirements relate to each other
4. **Consider Security**: Include security and privacy requirements
5. **Think About Testing**: Write testable requirements

### Reviewing AI Suggestions

1. **Evaluate Relevance**: Check if suggestions match your use case
2. **Verify Accuracy**: Ensure suggestions are technically correct
3. **Consider Impact**: Assess the impact of implementing suggestions
4. **Maintain Consistency**: Ensure suggestions align with existing requirements

### Improving Suggestions

1. **Provide Context**: Include more context in your specifications
2. **Use Examples**: Add examples to clarify requirements
3. **Be Specific**: Avoid vague or ambiguous language
4. **Include Constraints**: Specify performance, security, and other constraints

## Troubleshooting

### Common Issues

**Assistant not triggered:**

- Ensure PR has `needs-spec-review` label
- Check that markdown files are changed
- Verify OpenAI API key is configured

**No suggestions generated:**

- Check if markdown files contain specification content
- Verify OpenAI API is accessible
- Review PR diff for specification patterns

**Suggestions not relevant:**

- Provide more context in specifications
- Use clearer, more specific language
- Include examples and constraints

### Debug Commands

```bash
# Check if label is applied
gh pr view <PR_NUMBER> --json labels

# View workflow runs
gh run list --workflow=spec-ai.yaml

# Download workflow logs
gh run download <RUN_ID> --name ai-spec-metrics
```

## Future Enhancements

### Planned Features

1. **Multi-Model Support**: Support for different AI models
2. **Custom Rules**: Allow custom validation rules
3. **Learning from Feedback**: Improve suggestions based on acceptance rates
4. **Integration with Lean**: Direct integration with Lean theorem prover
5. **Visual Suggestions**: Graphical representation of requirement relationships

### Community Contributions

The AI Spec-Assistant is open to community contributions:

- **New Validation Rules**: Add custom specification validation
- **Improved Prompts**: Enhance AI prompt engineering
- **Additional Models**: Support for alternative AI models
- **Better Metrics**: Enhanced monitoring and reporting

## Support

For questions or issues with the AI Spec-Assistant:

- **GitHub Issues**: Report bugs or request features
- **Discord**: Real-time support and discussion
- **Documentation**: Check this guide for usage instructions
- **Community**: Ask questions in GitHub Discussions

---

_The AI Spec-Assistant is designed to improve specification quality and reduce the burden on human reviewers while maintaining high standards for formal verification._
