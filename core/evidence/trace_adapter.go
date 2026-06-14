// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package evidence

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

// TraceEvent is one step in a v0.1 execution trace.
type TraceEvent struct {
	Seq  int            `json:"seq"`
	Kind string         `json:"kind"`
	Meta map[string]any `json:",inline"`
}

// ExecutionTrace is the v0.1 execution-trace artifact shape.
type ExecutionTrace struct {
	SchemaVersion string       `json:"schema_version"`
	TraceID       string       `json:"trace_id"`
	Events        []TraceEvent `json:"events"`
	TraceDigest   string       `json:"trace_digest"`
}

type kitSimpleTrace struct {
	Name  string `json:"name"`
	Steps []struct {
		Op   string         `json:"op"`
		Tool string         `json:"tool,omitempty"`
		Args map[string]any `json:"args,omitempty"`
	} `json:"steps"`
}

type kitEventTrace struct {
	Metadata map[string]any `json:"metadata"`
	Events   []struct {
		ID      string         `json:"id"`
		Type    string         `json:"type"`
		Payload map[string]any `json:"payload,omitempty"`
	} `json:"events"`
}

// ImportKITTrace converts a TRACE-REPLAY-KIT trace JSON file into a v0.1 execution trace.
func ImportKITTrace(kitPath string, traceID string) (ExecutionTrace, error) {
	data, err := os.ReadFile(kitPath)
	if err != nil {
		return ExecutionTrace{}, fmt.Errorf("read kit trace: %w", err)
	}

	var raw map[string]any
	if err := json.Unmarshal(data, &raw); err != nil {
		return ExecutionTrace{}, fmt.Errorf("parse kit trace: %w", err)
	}

	events, idHint, err := mapKITToEvents(data)
	if err != nil {
		return ExecutionTrace{}, err
	}
	if len(events) == 0 {
		return ExecutionTrace{}, fmt.Errorf("kit trace produced no events")
	}
	if traceID == "" {
		traceID = idHint
		if traceID == "" {
			traceID = "kit-import"
		}
	}

	trace := ExecutionTrace{
		SchemaVersion: SchemaVersion,
		TraceID:       traceID,
		Events:        events,
	}
	digest, err := CanonicalJSONDigest(trace, "trace_digest")
	if err != nil {
		return ExecutionTrace{}, err
	}
	trace.TraceDigest = digest
	return trace, nil
}

func mapKITToEvents(data []byte) ([]TraceEvent, string, error) {
	var simple kitSimpleTrace
	if err := json.Unmarshal(data, &simple); err == nil && len(simple.Steps) > 0 {
		events := make([]TraceEvent, 0, len(simple.Steps))
		for i, step := range simple.Steps {
			kind := step.Op
			if step.Tool != "" {
				kind = step.Op + ":" + step.Tool
			}
			ev := TraceEvent{Seq: i, Kind: kind}
			if len(step.Args) > 0 {
				ev.Meta = map[string]any{"args": step.Args}
			}
			events = append(events, ev)
		}
		return events, simple.Name, nil
	}

	var eventTrace kitEventTrace
	if err := json.Unmarshal(data, &eventTrace); err != nil {
		return nil, "", fmt.Errorf("unsupported kit trace format")
	}
	if len(eventTrace.Events) == 0 {
		return nil, "", fmt.Errorf("kit trace missing steps or events")
	}
	events := make([]TraceEvent, 0, len(eventTrace.Events))
	nameHint := ""
	if eventTrace.Metadata != nil {
		if sys, ok := eventTrace.Metadata["system_info"].(map[string]any); ok {
			if n, ok := sys["name"].(string); ok {
				nameHint = n
			}
		}
	}
	for i, ev := range eventTrace.Events {
		kind := ev.Type
		if kind == "" {
			kind = "event"
		}
		item := TraceEvent{Seq: i, Kind: kind}
		if ev.ID != "" {
			item.Meta = map[string]any{"id": ev.ID}
		}
		if len(ev.Payload) > 0 {
			if item.Meta == nil {
				item.Meta = map[string]any{}
			}
			item.Meta["payload"] = ev.Payload
		}
		events = append(events, item)
	}
	return events, nameHint, nil
}

// WriteExecutionTrace writes an execution trace JSON file.
func WriteExecutionTrace(path string, trace ExecutionTrace) error {
	out, err := json.MarshalIndent(trace, "", "  ")
	if err != nil {
		return err
	}
	out = append(out, '\n')
	return os.WriteFile(path, out, 0644)
}

// MarshalTraceEvent implements custom JSON for inline meta fields.
func (e TraceEvent) MarshalJSON() ([]byte, error) {
	m := map[string]any{"seq": e.Seq, "kind": e.Kind}
	for k, v := range e.Meta {
		if k == "seq" || k == "kind" {
			continue
		}
		m[k] = v
	}
	return json.Marshal(m)
}

func (e *TraceEvent) UnmarshalJSON(data []byte) error {
	var raw map[string]any
	if err := json.Unmarshal(data, &raw); err != nil {
		return err
	}
	seqF, ok := raw["seq"].(float64)
	if !ok {
		return fmt.Errorf("event missing seq")
	}
	kind, ok := raw["kind"].(string)
	if !ok || strings.TrimSpace(kind) == "" {
		return fmt.Errorf("event missing kind")
	}
	e.Seq = int(seqF)
	e.Kind = kind
	delete(raw, "seq")
	delete(raw, "kind")
	if len(raw) > 0 {
		e.Meta = raw
	}
	return nil
}
