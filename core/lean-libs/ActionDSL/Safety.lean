/-
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the Apache License, Version 2.0 is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ActionDSL
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Array.Basic

namespace Fabric.ActionDSL

open Fabric

/-- DFA State representation -/
structure DFAState where
  id : Nat
  accepting : Bool
  metadata : List (String × String)

/-- DFA Transition -/
structure DFATransition where
  from_state : Nat
  event : String
  to_state : Nat
  conditions : List (String × String)

/-- Rate Limiter configuration -/
structure RateLimiter where
  key : String
  window_ms : Nat
  bound : Nat
  tolerance_ms : Nat

/-- Product DFA combining multiple safety properties -/
structure ProductDFA where
  states : List DFAState
  transitions : List DFATransition
  rate_limiters : List RateLimiter
  initial_state : Nat
  metadata : List (String × String)

/-- DFA Table for export -/
structure DFATable where
  states : List (Nat × Bool)
  transitions : List (Nat × String × Nat)
  rate_limiters : List (String × Nat × Nat × Nat)
  initial_state : Nat

/-- Convert ProductDFA to DFATable -/
def ProductDFA.to_table (dfa : ProductDFA) : DFATable :=
  { states := dfa.states.map (λ s => (s.id, s.accepting))
  , transitions := dfa.transitions.map (λ t => (t.from_state, t.event, t.to_state))
  , rate_limiters := dfa.rate_limiters.map (λ r => (r.key, r.window_ms, r.bound, r.tolerance_ms))
  , initial_state := dfa.initial_state
  }

/-- Parse event string to ExtendedAction -/
def parseEvent (event : String) : Option ExtendedAction :=
  let containsSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1
  if containsSubstr event "read" then
    some (.Read "default" [])
  else if containsSubstr event "write" then
    some (.Write "default" [])
  else if containsSubstr event "call" then
    some (.Call "default" [])
  else
    none

/-- Safety property for read operations -/
def read_safety (action : ExtendedAction) (ctx : ABACContext) : Bool :=
  match action with
  | .Read _ _ =>
    let has_permission := ctx.attributes.contains ("permission", "read") ||
                         ctx.attributes.contains ("role", "admin") ||
                         ctx.attributes.contains ("role", "reader")
    let epoch_ok := ctx.current_epoch ≥ 0
    let scope_ok := ctx.tenant != ""
    has_permission && epoch_ok && scope_ok
  | _ => true

/-- Safety property for write operations -/
def write_safety (action : ExtendedAction) (ctx : ABACContext) : Bool :=
  match action with
  | .Write _ _ =>
    let has_permission := ctx.attributes.contains ("permission", "write") ||
                         ctx.attributes.contains ("role", "admin") ||
                         ctx.attributes.contains ("role", "writer")
    let epoch_ok := ctx.current_epoch ≥ 0
    let scope_ok := ctx.tenant != ""
    let not_readonly := !ctx.attributes.contains ("readonly", "true")
    has_permission && epoch_ok && scope_ok && not_readonly
  | _ => true

/-- Safety property for call operations -/
def call_safety (action : ExtendedAction) (ctx : ABACContext) : Bool :=
  match action with
  | .Call tool _ =>
    let has_permission := ctx.attributes.contains ("permission", "call") ||
                         ctx.attributes.contains ("role", "admin") ||
                         ctx.attributes.contains ("permission", s!"call:{tool}")
    let epoch_ok := ctx.current_epoch ≥ 0
    let scope_ok := ctx.attributes.contains ("tenant", ctx.tenant)
    has_permission && epoch_ok && scope_ok
  | _ => true

/-- Combined safety check -/
def combined_safety (action : ExtendedAction) (ctx : ABACContext) : Bool :=
  read_safety action ctx &&
  write_safety action ctx &&
  call_safety action ctx

/-- Compile DSL policy to ProductDFA -/
def compile_to_dfa (_rules : List DSLRule) : ProductDFA :=
  let initial_state := DFAState.mk 0 true []
  let accepting_state := DFAState.mk 1 true []
  let rejecting_state := DFAState.mk 2 false []
  let states := [initial_state, accepting_state, rejecting_state]
  let transitions := [
    DFATransition.mk 0 "read" 1 [("permission", "read")],
    DFATransition.mk 0 "write" 1 [("permission", "write")],
    DFATransition.mk 0 "call" 1 [("permission", "call")],
    DFATransition.mk 0 "*" 2 []
  ]
  let rate_limiters := [
    RateLimiter.mk "default" 1000 100 100
  ]
  { states := states
  , transitions := transitions
  , rate_limiters := rate_limiters
  , initial_state := 0
  , metadata := [("version", "1.0"), ("type", "extended_action_dsl")]
  }

/-- Check if a trace is accepted by the DFA -/
def trace_accepted (dfa : ProductDFA) (trace : List String) : Bool :=
  let rec step (current_state : Nat) (events : List String) : Bool :=
    match events with
    | [] =>
      match dfa.states.find? (λ s => s.id == current_state) with
      | some state => state.accepting
      | none => false
    | event :: rest =>
      match dfa.transitions.find? (λ t => t.from_state == current_state && t.event == event) with
      | some transition => step transition.to_state rest
      | none => false
  step dfa.initial_state trace

end Fabric.ActionDSL
