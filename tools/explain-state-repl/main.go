// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"os"
	"strings"
	"time"
)

// Simple DFA structure for the REPL
type DFA struct {
	States       map[int]*DFAState `json:"states"`
	InitialState int               `json:"initial_state"`
	EventSet     map[string]bool   `json:"event_set"`
}

// DFAState represents a state in the DFA
type DFAState struct {
	ID          int                    `json:"id"`
	IsAccepting bool                   `json:"is_accepting"`
	Transitions map[string]int         `json:"transitions"`
	Metadata    map[string]interface{} `json:"metadata"`
}

// ExplainStateREPL provides an interactive REPL for DFA state analysis
type ExplainStateREPL struct {
	dfa     *DFA
	events  []string
	state   int
	history []StateTransition
	started bool
}

// StateTransition represents a state transition in the DFA
type StateTransition struct {
	Event       string    `json:"event"`
	FromState   int       `json:"from_state"`
	ToState     int       `json:"to_state"`
	IsAccepting bool      `json:"is_accepting"`
	Timestamp   time.Time `json:"timestamp"`
}

// EventAnalysis represents the analysis of an event
type EventAnalysis struct {
	Event        string    `json:"event"`
	CurrentState int       `json:"current_state"`
	NextState    int       `json:"next_state"`
	IsAccepting  bool      `json:"is_accepting"`
	Actions      []string  `json:"actions"`
	IsValid      bool      `json:"is_valid"`
	Message      string    `json:"message"`
	Timestamp    time.Time `json:"timestamp"`
}

func main() {
	fmt.Println("🔍 Provability Fabric - Explain State REPL")
	fmt.Println("==========================================")
	fmt.Println("Interactive DFA state analysis tool")
	fmt.Println("Type 'help' for commands, 'quit' to exit")
	fmt.Println()

	repl := &ExplainStateREPL{
		events:  make([]string, 0),
		history: make([]StateTransition, 0),
		started: false,
	}

	scanner := bufio.NewScanner(os.Stdin)
	for {
		fmt.Print("explain-state> ")
		if !scanner.Scan() {
			break
		}

		input := strings.TrimSpace(scanner.Text())
		if input == "" {
			continue
		}

		parts := strings.Fields(input)
		command := parts[0]

		switch command {
		case "help":
			showHelp()
		case "quit", "exit":
			fmt.Println("Goodbye!")
			return
		case "load":
			if len(parts) < 2 {
				fmt.Println("Usage: load <dfa-file.json>")
				continue
			}
			repl.loadDFA(parts[1])
		case "paste":
			if len(parts) < 2 {
				fmt.Println("Usage: paste <event>")
				continue
			}
			repl.pasteEvent(strings.Join(parts[1:], " "))
		case "reset":
			repl.reset()
		case "status":
			repl.showStatus()
		case "history":
			repl.showHistory()
		case "states":
			repl.showStates()
		case "transitions":
			repl.showTransitions()
		case "monni":
			repl.checkMonNI()
		case "json":
			repl.exportJSON()
		default:
			// Treat as event to analyze
			repl.pasteEvent(input)
		}
	}
}

func showHelp() {
	fmt.Println("Available commands:")
	fmt.Println("  help                    - Show this help")
	fmt.Println("  load <file>             - Load DFA from JSON file")
	fmt.Println("  paste <event>           - Analyze an event")
	fmt.Println("  reset                   - Reset to initial state")
	fmt.Println("  status                  - Show current state")
	fmt.Println("  history                 - Show transition history")
	fmt.Println("  states                  - List all DFA states")
	fmt.Println("  transitions             - Show possible transitions")
	fmt.Println("  monni                   - Check MonNI acceptance")
	fmt.Println("  json                    - Export analysis as JSON")
	fmt.Println("  quit/exit               - Exit the REPL")
	fmt.Println()
	fmt.Println("You can also paste events directly:")
	fmt.Println("  explain-state> call api")
	fmt.Println("  explain-state> access sensitive_data")
}

func (r *ExplainStateREPL) loadDFA(filename string) {
	data, err := os.ReadFile(filename)
	if err != nil {
		fmt.Printf("❌ Error loading DFA file: %v\n", err)
		return
	}

	var dfa DFA
	if err := json.Unmarshal(data, &dfa); err != nil {
		fmt.Printf("❌ Error parsing DFA JSON: %v\n", err)
		return
	}

	r.dfa = &dfa
	r.state = dfa.InitialState
	r.started = true
	r.events = make([]string, 0)
	r.history = make([]StateTransition, 0)

	fmt.Printf("✅ Loaded DFA with %d states (initial: %d)\n", len(dfa.States), dfa.InitialState)
	r.showCurrentState()
}

func (r *ExplainStateREPL) pasteEvent(event string) {
	if !r.started || r.dfa == nil {
		fmt.Println("❌ No DFA loaded. Use 'load <file>' first.")
		return
	}

	analysis := r.analyzeEvent(event)
	r.displayAnalysis(analysis)
}

func (r *ExplainStateREPL) analyzeEvent(event string) EventAnalysis {
	fromState := r.state

	// Get current state
	currentState, exists := r.dfa.States[r.state]
	if !exists {
		return EventAnalysis{
			Event:        event,
			CurrentState: r.state,
			IsValid:      false,
			Message:      "Invalid current state",
			Timestamp:    time.Now(),
		}
	}

	// Find next state
	nextState, hasTransition := currentState.Transitions[event]
	if !hasTransition {
		// Check for default transition
		if defaultState, hasDefault := currentState.Transitions["default"]; hasDefault {
			nextState = defaultState
			hasTransition = true
		}
	}

	if !hasTransition {
		return EventAnalysis{
			Event:        event,
			CurrentState: r.state,
			IsValid:      false,
			Message:      fmt.Sprintf("No transition found for event '%s'", event),
			Timestamp:    time.Now(),
		}
	}

	// Get next state info
	nextStateObj, exists := r.dfa.States[nextState]
	if !exists {
		return EventAnalysis{
			Event:        event,
			CurrentState: r.state,
			IsValid:      false,
			Message:      "Invalid next state",
			Timestamp:    time.Now(),
		}
	}

	// Get actions if available
	var actions []string
	if actionList, ok := nextStateObj.Metadata["actions"].([]string); ok {
		actions = actionList
	}

	// Record transition
	transition := StateTransition{
		Event:       event,
		FromState:   fromState,
		ToState:     nextState,
		IsAccepting: nextStateObj.IsAccepting,
		Timestamp:   time.Now(),
	}
	r.history = append(r.history, transition)

	// Update current state
	r.state = nextState
	r.events = append(r.events, event)

	return EventAnalysis{
		Event:        event,
		CurrentState: fromState,
		NextState:    nextState,
		IsAccepting:  nextStateObj.IsAccepting,
		Actions:      actions,
		IsValid:      true,
		Message:      fmt.Sprintf("Transitioned from state %d to state %d", fromState, nextState),
		Timestamp:    time.Now(),
	}
}

func (r *ExplainStateREPL) displayAnalysis(analysis EventAnalysis) {
	fmt.Printf("📊 Event Analysis: '%s'\n", analysis.Event)
	fmt.Printf("   Current State: %d\n", analysis.CurrentState)

	if analysis.IsValid {
		fmt.Printf("   Next State: %d\n", analysis.NextState)
		fmt.Printf("   Is Accepting: %t\n", analysis.IsAccepting)

		if len(analysis.Actions) > 0 {
			fmt.Printf("   Actions: %s\n", strings.Join(analysis.Actions, ", "))
		}

		// Check MonNI status
		monniStatus := r.checkMonNIForState(analysis.NextState)
		fmt.Printf("   MonNI Status: %s\n", monniStatus)

		if analysis.IsAccepting {
			fmt.Println("   ✅ State is accepting")
		} else {
			fmt.Println("   ⚠️  State is not accepting")
		}
	} else {
		fmt.Printf("   ❌ %s\n", analysis.Message)
	}

	fmt.Println()
}

func (r *ExplainStateREPL) checkMonNI() {
	if !r.started || r.dfa == nil {
		fmt.Println("❌ No DFA loaded.")
		return
	}

	status := r.checkMonNIForState(r.state)
	fmt.Printf("🔍 MonNI Status for current state %d: %s\n", r.state, status)
	fmt.Println()
}

func (r *ExplainStateREPL) checkMonNIForState(stateID int) string {
	state, exists := r.dfa.States[stateID]
	if !exists {
		return "Invalid state"
	}

	if state.IsAccepting {
		return "✅ MonNI remains in accept state"
	} else {
		return "❌ MonNI is not in accept state"
	}
}

func (r *ExplainStateREPL) reset() {
	if r.dfa != nil {
		r.state = r.dfa.InitialState
		r.events = make([]string, 0)
		r.history = make([]StateTransition, 0)
		fmt.Println("🔄 Reset to initial state")
		r.showCurrentState()
	} else {
		fmt.Println("❌ No DFA loaded.")
	}
}

func (r *ExplainStateREPL) showStatus() {
	if !r.started || r.dfa == nil {
		fmt.Println("❌ No DFA loaded.")
		return
	}

	r.showCurrentState()
	fmt.Printf("📈 Events processed: %d\n", len(r.events))
	fmt.Printf("📜 Transitions: %d\n", len(r.history))
	fmt.Println()
}

func (r *ExplainStateREPL) showCurrentState() {
	if !r.started || r.dfa == nil {
		return
	}

	state, exists := r.dfa.States[r.state]
	if !exists {
		fmt.Printf("❌ Invalid state: %d\n", r.state)
		return
	}

	fmt.Printf("📍 Current State: %d\n", r.state)
	fmt.Printf("   Type: %s\n", getStateType(state))
	fmt.Printf("   Accepting: %t\n", state.IsAccepting)

	if len(state.Transitions) > 0 {
		fmt.Printf("   Available transitions: %d\n", len(state.Transitions))
	}

	fmt.Println()
}

func (r *ExplainStateREPL) showHistory() {
	if len(r.history) == 0 {
		fmt.Println("📜 No transitions recorded")
		return
	}

	fmt.Println("📜 Transition History:")
	for i, transition := range r.history {
		fmt.Printf("  %d. '%s': %d → %d", i+1, transition.Event, transition.FromState, transition.ToState)
		if transition.IsAccepting {
			fmt.Print(" ✅")
		}
		fmt.Printf(" (%s)\n", transition.Timestamp.Format("15:04:05"))
	}
	fmt.Println()
}

func (r *ExplainStateREPL) showStates() {
	if !r.started || r.dfa == nil {
		fmt.Println("❌ No DFA loaded.")
		return
	}

	fmt.Println("🗺️  DFA States:")
	for id, state := range r.dfa.States {
		stateType := getStateType(state)
		marker := ""
		if id == r.state {
			marker = " ← current"
		}
		if id == r.dfa.InitialState {
			marker += " (initial)"
		}

		fmt.Printf("  State %d: %s%s\n", id, stateType, marker)
		if state.IsAccepting {
			fmt.Printf("    ✅ Accepting state")
			if actions, ok := state.Metadata["actions"].([]string); ok && len(actions) > 0 {
				fmt.Printf(" (actions: %s)", strings.Join(actions, ", "))
			}
			fmt.Println()
		}
	}
	fmt.Println()
}

func (r *ExplainStateREPL) showTransitions() {
	if !r.started || r.dfa == nil {
		fmt.Println("❌ No DFA loaded.")
		return
	}

	state, exists := r.dfa.States[r.state]
	if !exists {
		fmt.Printf("❌ Invalid current state: %d\n", r.state)
		return
	}

	fmt.Printf("🔄 Transitions from current state %d:\n", r.state)
	if len(state.Transitions) == 0 {
		fmt.Println("  No transitions available")
	} else {
		for event, nextState := range state.Transitions {
			nextStateObj := r.dfa.States[nextState]
			accepting := ""
			if nextStateObj.IsAccepting {
				accepting = " ✅"
			}
			fmt.Printf("  '%s' → State %d%s\n", event, nextState, accepting)
		}
	}
	fmt.Println()
}

func (r *ExplainStateREPL) exportJSON() {
	if !r.started || r.dfa == nil {
		fmt.Println("❌ No DFA loaded.")
		return
	}

	export := map[string]interface{}{
		"current_state": r.state,
		"events":        r.events,
		"history":       r.history,
		"monni_status":  r.checkMonNIForState(r.state),
		"exported_at":   time.Now(),
	}

	data, err := json.MarshalIndent(export, "", "  ")
	if err != nil {
		fmt.Printf("❌ Error exporting JSON: %v\n", err)
		return
	}

	fmt.Println("📄 JSON Export:")
	fmt.Println(string(data))
	fmt.Println()
}

func getStateType(state *DFAState) string {
	if state.IsAccepting {
		return "accepting"
	}
	if len(state.Transitions) == 0 {
		return "terminal"
	}
	return "intermediate"
}
