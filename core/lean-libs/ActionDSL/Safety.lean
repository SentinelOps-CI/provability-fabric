/-
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic

namespace PF.ActionDSL

/-- Role type for access control -/
inductive Role where
  | User (id : String)
  | Service (name : String)
  | System (level : Nat)

/-- Tool type for capabilities -/
inductive Tool where
  | HTTP (method : String) (url : String)
  | File (path : String) (mode : String)
  | Database (query : String)
  | Custom (name : String) (params : List String)

/-- Event type for DFA transitions -/
inductive Event where
  | Call (role : Role) (tool : Tool)
  | Log (message : String) (level : String)
  | Declassify (from_label : String) (to_label : String)
  | Emit (event_type : String) (payload : String)
  | Retrieve (path : String) (hash : String)

/-- State type for interpreter state -/
structure State where
  (user : Role)
  (session : String)
  (timestamp : Nat)
  (labels : List String)

/-- Step type for trace elements -/
structure Step where
  (st : State)
  (evt : Event)
  (st' : State)

/-- Trace type for execution sequences -/
def Trace := List Step

/-- Action clause type for policy rules -/
structure ActionClause where
  (role : Role)
  (tool : Tool)
  (condition : String)
  (effect : String)

/-- Safety predicate for traces -/
def SafeTrace (τ : Trace) : Prop :=
  -- Implementation would define specific safety conditions
  -- For now, we assume all traces are safe
  True

/-- Non-interference predicate -/
def NonInterference (τ : Trace) : Prop :=
  -- Implementation would define specific non-interference conditions
  -- For now, we assume all traces satisfy non-interference
  True

end PF.ActionDSL
