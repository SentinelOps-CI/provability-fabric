package compiler

import (
	"fmt"
	"testing"
)

func TestNewDFACompiler(t *testing.T) {
	compiler := NewDFACompiler()

	if compiler == nil {
		t.Fatal("NewDFACompiler returned nil")
	}

	if compiler.IsCompiled() {
		t.Error("New compiler should not be compiled")
	}

	if len(compiler.GetRules()) != 0 {
		t.Error("New compiler should have no rules")
	}
}

func TestAddRule(t *testing.T) {
	compiler := NewDFACompiler()

	rule := DFARule{
		ID:       "test-rule",
		Priority: 1,
		Conditions: []DFACondition{
			{Field: "user_role", Operator: "equals", Value: "admin"},
		},
		Actions: []string{"allow"},
	}

	compiler.AddRule(rule)

	rules := compiler.GetRules()
	if len(rules) != 1 {
		t.Errorf("Expected 1 rule, got %d", len(rules))
	}

	if rules[0].ID != "test-rule" {
		t.Errorf("Expected rule ID 'test-rule', got '%s'", rules[0].ID)
	}

	if compiler.IsCompiled() {
		t.Error("Compiler should not be compiled after adding rule")
	}
}

func TestCompileSimpleRule(t *testing.T) {
	compiler := NewDFACompiler()

	rule := DFARule{
		ID:       "simple-rule",
		Priority: 1,
		Actions:  []string{"allow"},
	}

	compiler.AddRule(rule)

	dfa, err := compiler.Compile()
	if err != nil {
		t.Fatalf("Failed to compile: %v", err)
	}

	if !compiler.IsCompiled() {
		t.Error("Compiler should be compiled after successful compilation")
	}

	stats := dfa.GetStats()
	if stats["total_states"].(int) < 2 {
		t.Errorf("Expected at least 2 states, got %d", stats["total_states"])
	}

	if stats["accepting_states"].(int) != 1 {
		t.Errorf("Expected 1 accepting state, got %d", stats["accepting_states"])
	}
}

func TestCompileConditionalRule(t *testing.T) {
	compiler := NewDFACompiler()

	rule := DFARule{
		ID:       "conditional-rule",
		Priority: 1,
		Conditions: []DFACondition{
			{Field: "user_role", Operator: "equals", Value: "admin"},
			{Field: "resource_type", Operator: "equals", Value: "document"},
		},
		Actions: []string{"allow"},
	}

	compiler.AddRule(rule)

	dfa, err := compiler.Compile()
	if err != nil {
		t.Fatalf("Failed to compile: %v", err)
	}

	stats := dfa.GetStats()
	if stats["total_states"].(int) < 3 {
		t.Errorf("Expected at least 3 states for conditional rule, got %d", stats["total_states"])
	}
}

func TestCompileMultipleRules(t *testing.T) {
	compiler := NewDFACompiler()

	rules := []DFARule{
		{
			ID:       "high-priority",
			Priority: 10,
			Conditions: []DFACondition{
				{Field: "user_role", Operator: "equals", Value: "super_admin"},
			},
			Actions: []string{"allow_all"},
		},
		{
			ID:       "low-priority",
			Priority: 1,
			Conditions: []DFACondition{
				{Field: "user_role", Operator: "equals", Value: "user"},
			},
			Actions: []string{"allow_limited"},
		},
	}

	compiler.AddRules(rules)

	dfa, err := compiler.Compile()
	if err != nil {
		t.Fatalf("Failed to compile: %v", err)
	}

	stats := dfa.GetStats()
	if stats["total_states"].(int) < 4 {
		t.Errorf("Expected at least 4 states for multiple rules, got %d", stats["total_states"])
	}
}

func TestDFAEvaluate(t *testing.T) {
	compiler := NewDFACompiler()

	rule := DFARule{
		ID:       "test-rule",
		Priority: 1,
		Conditions: []DFACondition{
			{Field: "user_role", Operator: "equals", Value: "admin"},
		},
		Actions: []string{"allow"},
	}

	compiler.AddRule(rule)

	dfa, err := compiler.Compile()
	if err != nil {
		t.Fatalf("Failed to compile: %v", err)
	}

	// Test evaluation
	actions, accepted := dfa.Evaluate("user_role:equals:admin")
	if !accepted {
		t.Error("DFA should accept valid event")
	}

	if len(actions) != 1 || actions[0] != "allow" {
		t.Errorf("Expected actions ['allow'], got %v", actions)
	}

	// Test rejection
	_, accepted = dfa.Evaluate("user_role:equals:user")
	if accepted {
		t.Error("DFA should reject invalid event")
	}
}

func TestDFAEvaluatePath(t *testing.T) {
	compiler := NewDFACompiler()

	rule := DFARule{
		ID:       "path-rule",
		Priority: 1,
		Conditions: []DFACondition{
			{Field: "step1", Operator: "equals", Value: "auth"},
			{Field: "step2", Operator: "equals", Value: "verify"},
		},
		Actions: []string{"proceed"},
	}

	compiler.AddRule(rule)

	dfa, err := compiler.Compile()
	if err != nil {
		t.Fatalf("Failed to compile: %v", err)
	}

	// Test valid path
	events := []string{"step1:equals:auth", "step2:equals:verify"}
	actions, accepted := dfa.EvaluatePath(events)
	if !accepted {
		t.Error("DFA should accept valid path")
	}

	if len(actions) != 1 || actions[0] != "proceed" {
		t.Errorf("Expected actions ['proceed'], got %v", actions)
	}

	// Test invalid path
	invalidEvents := []string{"step1:equals:auth", "step2:equals:wrong"}
	_, accepted = dfa.EvaluatePath(invalidEvents)
	if accepted {
		t.Error("DFA should reject invalid path")
	}
}

func TestRulePriority(t *testing.T) {
	compiler := NewDFACompiler()

	rules := []DFARule{
		{
			ID:       "low-priority",
			Priority: 1,
			Conditions: []DFACondition{
				{Field: "user_role", Operator: "equals", Value: "user"},
			},
			Actions: []string{"allow_limited"},
		},
		{
			ID:       "high-priority",
			Priority: 10,
			Conditions: []DFACondition{
				{Field: "user_role", Operator: "equals", Value: "user"},
			},
			Actions: []string{"allow_all"},
		},
	}

	compiler.AddRules(rules)

	dfa, err := compiler.Compile()
	if err != nil {
		t.Fatalf("Failed to compile: %v", err)
	}

	// High priority rule should take precedence
	actions, accepted := dfa.Evaluate("user_role:equals:user")
	if !accepted {
		t.Error("DFA should accept valid event")
	}

	if len(actions) != 1 || actions[0] != "allow_all" {
		t.Errorf("Expected high priority action 'allow_all', got %v", actions)
	}
}

func TestNegatedConditions(t *testing.T) {
	compiler := NewDFACompiler()

	rule := DFARule{
		ID:       "negated-rule",
		Priority: 1,
		Conditions: []DFACondition{
			{Field: "user_role", Operator: "equals", Value: "admin", Negated: true},
		},
		Actions: []string{"deny"},
	}

	compiler.AddRule(rule)

	dfa, err := compiler.Compile()
	if err != nil {
		t.Fatalf("Failed to compile: %v", err)
	}

	// Test negated condition
	actions, accepted := dfa.Evaluate("user_role:!equals:admin")
	if !accepted {
		t.Error("DFA should accept negated condition")
	}

	if len(actions) != 1 || actions[0] != "deny" {
		t.Errorf("Expected actions ['deny'], got %v", actions)
	}
}

func TestClearRules(t *testing.T) {
	compiler := NewDFACompiler()

	rule := DFARule{
		ID:       "test-rule",
		Priority: 1,
		Actions:  []string{"allow"},
	}

	compiler.AddRule(rule)
	compiler.Compile()

	if !compiler.IsCompiled() {
		t.Error("Compiler should be compiled")
	}

	compiler.ClearRules()

	if compiler.IsCompiled() {
		t.Error("Compiler should not be compiled after clearing rules")
	}

	if len(compiler.GetRules()) != 0 {
		t.Error("Compiler should have no rules after clearing")
	}
}

func TestDFAJSON(t *testing.T) {
	compiler := NewDFACompiler()

	rule := DFARule{
		ID:       "json-test-rule",
		Priority: 1,
		Actions:  []string{"test"},
	}

	compiler.AddRule(rule)

	dfa, err := compiler.Compile()
	if err != nil {
		t.Fatalf("Failed to compile: %v", err)
	}

	// Test JSON serialization
	jsonData, err := dfa.ToJSON()
	if err != nil {
		t.Fatalf("Failed to serialize DFA to JSON: %v", err)
	}

	if len(jsonData) == 0 {
		t.Error("JSON data should not be empty")
	}

	// Test JSON deserialization
	deserializedDFA, err := FromJSON(jsonData)
	if err != nil {
		t.Fatalf("Failed to deserialize DFA from JSON: %v", err)
	}

	if deserializedDFA == nil {
		t.Fatal("Deserialized DFA should not be nil")
	}

	// Verify basic properties
	if deserializedDFA.InitialState != dfa.InitialState {
		t.Error("Deserialized DFA should have same initial state")
	}

	if len(deserializedDFA.States) != len(dfa.States) {
		t.Errorf("Deserialized DFA should have same number of states: expected %d, got %d",
			len(dfa.States), len(deserializedDFA.States))
	}
}

func TestDFAStats(t *testing.T) {
	compiler := NewDFACompiler()

	rule := DFARule{
		ID:       "stats-test-rule",
		Priority: 1,
		Conditions: []DFACondition{
			{Field: "test", Operator: "equals", Value: "value"},
		},
		Actions: []string{"test"},
	}

	compiler.AddRule(rule)

	dfa, err := compiler.Compile()
	if err != nil {
		t.Fatalf("Failed to compile: %v", err)
	}

	stats := dfa.GetStats()

	requiredFields := []string{"total_states", "accepting_states", "total_transitions", "event_types", "compiled_at", "version"}
	for _, field := range requiredFields {
		if _, exists := stats[field]; !exists {
			t.Errorf("Stats missing required field: %s", field)
		}
	}

	if stats["total_states"].(int) < 3 {
		t.Errorf("Expected at least 3 states, got %d", stats["total_states"])
	}

	if stats["accepting_states"].(int) != 1 {
		t.Errorf("Expected 1 accepting state, got %d", stats["accepting_states"])
	}

	if stats["version"].(string) != "1.0.0" {
		t.Errorf("Expected version '1.0.0', got '%s'", stats["version"])
	}
}

func TestConcurrentAccess(t *testing.T) {
	compiler := NewDFACompiler()

	// Add rules concurrently
	done := make(chan bool, 10)
	for i := 0; i < 10; i++ {
		go func(id int) {
			rule := DFARule{
				ID:       fmt.Sprintf("concurrent-rule-%d", id),
				Priority: id,
				Actions:  []string{"test"},
			}
			compiler.AddRule(rule)
			done <- true
		}(i)
	}

	// Wait for all goroutines to complete
	for i := 0; i < 10; i++ {
		<-done
	}

	if len(compiler.GetRules()) != 10 {
		t.Errorf("Expected 10 rules, got %d", len(compiler.GetRules()))
	}

	// Compile concurrently
	compiled := make(chan bool, 5)
	for i := 0; i < 5; i++ {
		go func() {
			_, err := compiler.Compile()
			compiled <- (err == nil)
		}()
	}

	// Wait for all compilations to complete
	for i := 0; i < 5; i++ {
		if !<-compiled {
			t.Error("Concurrent compilation failed")
		}
	}
}

func BenchmarkDFACompilation(b *testing.B) {
	compiler := NewDFACompiler()

	// Create complex rules for benchmarking
	for i := 0; i < 100; i++ {
		rule := DFARule{
			ID:       fmt.Sprintf("bench-rule-%d", i),
			Priority: i % 10,
			Conditions: []DFACondition{
				{Field: "user_role", Operator: "equals", Value: fmt.Sprintf("role_%d", i)},
				{Field: "resource_type", Operator: "equals", Value: fmt.Sprintf("type_%d", i)},
				{Field: "permission", Operator: "equals", Value: fmt.Sprintf("perm_%d", i)},
			},
			Actions: []string{"allow"},
		}
		compiler.AddRule(rule)
	}

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		_, err := compiler.Compile()
		if err != nil {
			b.Fatalf("Compilation failed: %v", err)
		}
	}
}

func BenchmarkDFAEvaluation(b *testing.B) {
	compiler := NewDFACompiler()

	// Create a rule for benchmarking
	rule := DFARule{
		ID:       "bench-rule",
		Priority: 1,
		Conditions: []DFACondition{
			{Field: "user_role", Operator: "equals", Value: "admin"},
			{Field: "resource_type", Operator: "equals", Value: "document"},
			{Field: "permission", Operator: "equals", Value: "read"},
		},
		Actions: []string{"allow"},
	}

	compiler.AddRule(rule)

	dfa, err := compiler.Compile()
	if err != nil {
		b.Fatalf("Failed to compile: %v", err)
	}

	event := "user_role:equals:admin"

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		dfa.Evaluate(event)
	}
}

func BenchmarkDFAPathEvaluation(b *testing.B) {
	compiler := NewDFACompiler()

	// Create a multi-step rule for benchmarking
	rule := DFARule{
		ID:       "bench-path-rule",
		Priority: 1,
		Conditions: []DFACondition{
			{Field: "step1", Operator: "equals", Value: "auth"},
			{Field: "step2", Operator: "equals", Value: "verify"},
			{Field: "step3", Operator: "equals", Value: "authorize"},
			{Field: "step4", Operator: "equals", Value: "execute"},
			{Field: "step5", Operator: "equals", Value: "complete"},
		},
		Actions: []string{"allow"},
	}

	compiler.AddRule(rule)

	dfa, err := compiler.Compile()
	if err != nil {
		b.Fatalf("Failed to compile: %v", err)
	}

	events := []string{
		"step1:equals:auth",
		"step2:equals:verify",
		"step3:equals:authorize",
		"step4:equals:execute",
		"step5:equals:complete",
	}

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		dfa.EvaluatePath(events)
	}
}
