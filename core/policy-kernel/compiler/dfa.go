package compiler

import (
	"encoding/json"
	"fmt"
	"sort"
	"strings"
	"sync"
	"time"
)

// DFAState represents a state in the deterministic finite automaton
type DFAState struct {
	ID          int                    `json:"id"`
	IsAccepting bool                   `json:"is_accepting"`
	Transitions map[string]int         `json:"transitions"` // event -> next_state_id
	Metadata    map[string]interface{} `json:"metadata"`
}

// DFA represents the compiled deterministic finite automaton
type DFA struct {
	States       map[int]*DFAState `json:"states"`
	InitialState int               `json:"initial_state"`
	EventSet     map[string]bool   `json:"event_set"`
	CompiledAt   time.Time         `json:"compiled_at"`
	Version      string            `json:"version"`
	mu           sync.RWMutex
}

// DFARule represents a policy rule that can be compiled into the DFA
type DFARule struct {
	ID         string                 `json:"id"`
	Priority   int                    `json:"priority"`
	Conditions []DFACondition         `json:"conditions"`
	Actions    []string               `json:"actions"`
	Metadata   map[string]interface{} `json:"metadata"`
}

// DFACondition represents a condition that must be met for a rule to apply
type DFACondition struct {
	Field    string      `json:"field"`
	Operator string      `json:"operator"`
	Value    interface{} `json:"value"`
	Negated  bool        `json:"negated"`
}

// DFACompiler compiles policy rules into a DFA
type DFACompiler struct {
	rules    []DFARule
	dfa      *DFA
	compiled bool
	mu       sync.RWMutex
}

// NewDFACompiler creates a new DFA compiler
func NewDFACompiler() *DFACompiler {
	return &DFACompiler{
		rules:    make([]DFARule, 0),
		dfa:      nil,
		compiled: false,
	}
}

// AddRule adds a policy rule to the compiler
func (c *DFACompiler) AddRule(rule DFARule) {
	c.mu.Lock()
	defer c.mu.Unlock()

	// Reset compiled state when rules change
	c.compiled = false
	c.dfa = nil

	c.rules = append(c.rules, rule)
}

// AddRules adds multiple policy rules to the compiler
func (c *DFACompiler) AddRules(rules []DFARule) {
	c.mu.Lock()
	defer c.mu.Unlock()

	// Reset compiled state when rules change
	c.compiled = false
	c.dfa = nil

	c.rules = append(c.rules, rules...)
}

// Compile compiles the rules into a DFA
func (c *DFACompiler) Compile() (*DFA, error) {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.compiled && c.dfa != nil {
		return c.dfa, nil
	}

	// Sort rules by priority (higher priority first)
	sort.Slice(c.rules, func(i, j int) bool {
		return c.rules[i].Priority > c.rules[j].Priority
	})

	dfa := &DFA{
		States:       make(map[int]*DFAState),
		InitialState: 0,
		EventSet:     make(map[string]bool),
		CompiledAt:   time.Now(),
		Version:      "1.0.0",
	}

	// Create initial state
	initialState := &DFAState{
		ID:          0,
		IsAccepting: false,
		Transitions: make(map[string]int),
		Metadata:    make(map[string]interface{}),
	}
	dfa.States[0] = initialState

	// Build DFA from rules
	nextStateID := 1
	for _, rule := range c.rules {
		if err := c.compileRule(dfa, &rule, 0, &nextStateID); err != nil {
			return nil, fmt.Errorf("failed to compile rule %s: %w", rule.ID, err)
		}
	}

	// Mark accepting states
	c.markAcceptingStates(dfa)

	c.dfa = dfa
	c.compiled = true

	return dfa, nil
}

// compileRule compiles a single rule into the DFA
func (c *DFACompiler) compileRule(dfa *DFA, rule *DFARule, currentState int, nextStateID *int) error {
	if len(rule.Conditions) == 0 {
		// No conditions, create accepting state
		acceptingState := &DFAState{
			ID:          *nextStateID,
			IsAccepting: true,
			Transitions: make(map[string]int),
			Metadata: map[string]interface{}{
				"rule_id":  rule.ID,
				"actions":  rule.Actions,
				"priority": rule.Priority,
			},
		}
		dfa.States[*nextStateID] = acceptingState

		// Add transition from current state to accepting state
		event := c.createEventKey(rule.Conditions)
		dfa.States[currentState].Transitions[event] = *nextStateID
		dfa.EventSet[event] = true

		*nextStateID++
		return nil
	}

	// Compile conditions into state transitions
	return c.compileConditions(dfa, rule, currentState, nextStateID, rule.Conditions, 0)
}

// compileConditions compiles conditions into state transitions
func (c *DFACompiler) compileConditions(
	dfa *DFA,
	rule *DFARule,
	currentState int,
	nextStateID *int,
	conditions []DFACondition,
	conditionIndex int,
) error {
	if conditionIndex >= len(conditions) {
		// All conditions satisfied, create accepting state
		acceptingState := &DFAState{
			ID:          *nextStateID,
			IsAccepting: true,
			Transitions: make(map[string]int),
			Metadata: map[string]interface{}{
				"rule_id":  rule.ID,
				"actions":  rule.Actions,
				"priority": rule.Priority,
			},
		}
		dfa.States[*nextStateID] = acceptingState

		// Add transition from current state to accepting state
		event := "condition_satisfied"
		dfa.States[currentState].Transitions[event] = *nextStateID
		dfa.EventSet[event] = true

		*nextStateID++
		return nil
	}

	condition := conditions[conditionIndex]
	event := c.createConditionEvent(&condition)

	// Check if transition already exists
	if nextState, exists := dfa.States[currentState].Transitions[event]; exists {
		// Follow existing transition
		return c.compileConditions(dfa, rule, nextState, nextStateID, conditions, conditionIndex+1)
	}

	// Create new intermediate state
	intermediateState := &DFAState{
		ID:          *nextStateID,
		IsAccepting: false,
		Transitions: make(map[string]int),
		Metadata: map[string]interface{}{
			"condition_index": conditionIndex,
			"rule_id":         rule.ID,
		},
	}
	dfa.States[*nextStateID] = intermediateState

	// Add transition from current state to intermediate state
	dfa.States[currentState].Transitions[event] = *nextStateID
	dfa.EventSet[event] = true

	// Continue compiling conditions from intermediate state
	*nextStateID++
	return c.compileConditions(dfa, rule, *nextStateID-1, nextStateID, conditions, conditionIndex+1)
}

// createConditionEvent creates an event key for a condition
func (c *DFACompiler) createConditionEvent(condition *DFACondition) string {
	operator := condition.Operator
	if condition.Negated {
		operator = "!" + operator
	}

	return fmt.Sprintf("%s:%s:%v", condition.Field, operator, condition.Value)
}

// createEventKey creates an event key for a set of conditions
func (c *DFACompiler) createEventKey(conditions []DFACondition) string {
	if len(conditions) == 0 {
		return "no_conditions"
	}

	parts := make([]string, len(conditions))
	for i, condition := range conditions {
		parts[i] = c.createConditionEvent(&condition)
	}

	sort.Strings(parts)
	return strings.Join(parts, "|")
}

// markAcceptingStates marks states as accepting based on rule priorities
func (c *DFACompiler) markAcceptingStates(dfa *DFA) {
	// Group states by rule ID to handle conflicts
	ruleStates := make(map[string][]*DFAState)

	for _, state := range dfa.States {
		if state.IsAccepting {
			if ruleID, ok := state.Metadata["rule_id"].(string); ok {
				ruleStates[ruleID] = append(ruleStates[ruleID], state)
			}
		}
	}

	// For each rule, keep only the highest priority accepting state
	for ruleID, states := range ruleStates {
		if len(states) > 1 {
			// Sort by priority (higher first)
			sort.Slice(states, func(i, j int) bool {
				priorityI, _ := states[i].Metadata["priority"].(int)
				priorityJ, _ := states[j].Metadata["priority"].(int)
				return priorityI > priorityJ
			})

			// Mark only the highest priority state as accepting
			for i, state := range states {
				state.IsAccepting = (i == 0)
			}
		}
	}
}

// Evaluate evaluates an event against the compiled DFA
func (dfa *DFA) Evaluate(event string) ([]string, bool) {
	dfa.mu.RLock()
	defer dfa.mu.RUnlock()

	currentState := dfa.InitialState

	for {
		state, exists := dfa.States[currentState]
		if !exists {
			return nil, false
		}

		// Check if this is an accepting state
		if state.IsAccepting {
			if actions, ok := state.Metadata["actions"].([]string); ok {
				return actions, true
			}
			return nil, true
		}

		// Follow transition
		nextState, exists := state.Transitions[event]
		if !exists {
			// No transition found, check for default transitions
			if defaultState, exists := state.Transitions["default"]; exists {
				currentState = defaultState
				continue
			}
			return nil, false
		}

		currentState = nextState
	}
}

// EvaluatePath evaluates a sequence of events against the DFA
func (dfa *DFA) EvaluatePath(events []string) ([]string, bool) {
	dfa.mu.RLock()
	defer dfa.mu.RUnlock()

	currentState := dfa.InitialState

	for _, event := range events {
		state, exists := dfa.States[currentState]
		if !exists {
			return nil, false
		}

		// Check if this is an accepting state
		if state.IsAccepting {
			if actions, ok := state.Metadata["actions"].([]string); ok {
				return actions, true
			}
			return nil, true
		}

		// Follow transition
		nextState, exists := state.Transitions[event]
		if !exists {
			// No transition found, check for default transitions
			if defaultState, exists := state.Transitions["default"]; exists {
				currentState = defaultState
				continue
			}
			return nil, false
		}

		currentState = nextState
	}

	// Check final state
	if finalState, exists := dfa.States[currentState]; exists && finalState.IsAccepting {
		if actions, ok := finalState.Metadata["actions"].([]string); ok {
			return actions, true
		}
		return nil, true
	}

	return nil, false
}

// GetStats returns statistics about the DFA
func (dfa *DFA) GetStats() map[string]interface{} {
	dfa.mu.RLock()
	defer dfa.mu.RUnlock()

	stats := make(map[string]interface{})
	stats["total_states"] = len(dfa.States)
	stats["accepting_states"] = 0
	stats["total_transitions"] = 0
	stats["event_types"] = len(dfa.EventSet)
	stats["compiled_at"] = dfa.CompiledAt
	stats["version"] = dfa.Version

	for _, state := range dfa.States {
		if state.IsAccepting {
			stats["accepting_states"] = stats["accepting_states"].(int) + 1
		}
		stats["total_transitions"] = stats["total_transitions"].(int) + len(state.Transitions)
	}

	return stats
}

// ToJSON converts the DFA to JSON representation
func (dfa *DFA) ToJSON() ([]byte, error) {
	dfa.mu.RLock()
	defer dfa.mu.RUnlock()

	return json.MarshalIndent(dfa, "", "  ")
}

// FromJSON creates a DFA from JSON representation
func FromJSON(data []byte) (*DFA, error) {
	var dfa DFA
	if err := json.Unmarshal(data, &dfa); err != nil {
		return nil, fmt.Errorf("failed to unmarshal DFA: %w", err)
	}
	return &dfa, nil
}

// IsCompiled returns whether the compiler has compiled rules
func (c *DFACompiler) IsCompiled() bool {
	c.mu.RLock()
	defer c.mu.RUnlock()
	return c.compiled
}

// GetRules returns a copy of the current rules
func (c *DFACompiler) GetRules() []DFARule {
	c.mu.RLock()
	defer c.mu.RUnlock()

	rules := make([]DFARule, len(c.rules))
	copy(rules, c.rules)
	return rules
}

// ClearRules clears all rules and resets the compiler
func (c *DFACompiler) ClearRules() {
	c.mu.Lock()
	defer c.mu.Unlock()

	c.rules = make([]DFARule, 0)
	c.compiled = false
	c.dfa = nil
}
