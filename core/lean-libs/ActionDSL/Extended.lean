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
import Mathlib.Data.Option.Basic
import Mathlib.Logic.Basic

namespace PF.ActionDSL

/-- Extended Role type with ABAC support -/
inductive Role where
  | User (id : String)
  | Service (name : String)
  | System (level : Nat)
  | Tenant (name : String)
  | Group (name : String)

/-- Extended Tool type for capabilities -/
inductive Tool where
  | HTTP (method : String) (url : String)
  | File (path : String) (mode : String)
  | Database (query : String)
  | Custom (name : String) (params : List String)
  | Email (to : String) (subject : String)
  | Log (level : String) (message : String)

/-- Document identifier for read/write operations -/
structure Document where
  id : String
  path : List String
  version : Nat
  deriving Repr, BEq

/-- Extended Event type including read/write operations -/
inductive Event where
  | Call (role : Role) (tool : Tool)
  | Read (role : Role) (doc : Document) (path : List String)
  | Write (role : Role) (doc : Document) (path : List String)
  | Log (message : String) (level : String)
  | Declassify (from_label : String) (to_label : String)
  | Emit (event_type : String) (payload : String)
  | Retrieve (path : String) (hash : String)

/-- ABAC attribute types -/
inductive Attribute where
  | String (key : String) (value : String)
  | Number (key : String) (value : Nat)
  | Boolean (key : String) (value : Bool)
  | List (key : String) (values : List String)

/-- Session information for ABAC -/
structure Session where
  id : String
  user_id : String
  tenant : String
  created_at : Nat
  expires_at : Nat
  attributes : List Attribute
  deriving Repr

/-- Epoch range for temporal ABAC -/
structure EpochRange where
  start : Nat
  end : Nat
  deriving Repr

/-- Scope for multi-tenant isolation -/
structure Scope where
  tenant : String
  project : String
  environment : String
  deriving Repr

/-- ABAC guard predicates with specific primitives as required -/
inductive Guard where
  | True
  | False
  | And (left : Guard) (right : Guard)
  | Or (left : Guard) (right : Guard)
  | Not (guard : Guard)
  | HasRole (role : String)
  | HasAttribute (key : String) (value : String)
  | SessionAttribute (key : String) (value : String)
  | EpochIn (range : EpochRange)
  | ScopeMatch (scope : Scope)
  | StringEquals (left : String) (right : String)
  | StringContains (haystack : String) (needle : String)
  | NumberEquals (left : Nat) (right : Nat)
  | NumberLessThan (left : Nat) (right : Nat)
  | NumberGreaterThan (left : Nat) (right : Nat)
  -- New ABAC primitives as specified
  | Attr (key : String)  -- attr("k") primitive
  | Session (key : String)  -- session("k") primitive
  | EpochInRange (start : Nat) (end : Nat)  -- epoch_in [s,e] primitive
  | Scope (tenant : String)  -- scope("tenantA") primitive

/-- Extended Action clause with ABAC guards for read/write -/
structure ActionClause where
  action : String  -- "allow" or "forbid"
  role : Role
  operation : Event
  guard : Guard
  deriving Repr

/-- DSL Grammar extensions for read/write events -/
structure DSLRule where
  name : String
  description : String
  -- Allow Role:"X" : Tool:"T" when pre(u, γ)
  allow_call : Option (Role × Tool × Guard)
  -- Allow read(doc,path) when Φ
  allow_read : Option (Role × Document × List String × Guard)
  -- Forbid write(doc,path) when Φ
  forbid_write : Option (Role × Document × List String × Guard)
  -- General allow/forbid clauses
  clauses : List ActionClause
  priority : Nat
  deriving Repr

/-- Policy rule -/
structure PolicyRule where
  name : String
  description : String
  clauses : List ActionClause
  priority : Nat
  deriving Repr

/-- State type for interpreter state -/
structure State where
  user : Role
  session : Session
  timestamp : Nat
  labels : List String
  attributes : List Attribute
  scope : Scope
  deriving Repr

/-- Step type for trace elements -/
structure Step where
  st : State
  evt : Event
  st' : State
  deriving Repr

/-- Trace type for execution sequences -/
def Trace := List Step

/-- Evaluate a guard predicate with new ABAC primitives -/
def evalGuard (guard : Guard) (state : State) : Bool :=
  match guard with
  | Guard.True => true
  | Guard.False => false
  | Guard.And left right => evalGuard left state && evalGuard right state
  | Guard.Or left right => evalGuard left state || evalGuard right state
  | Guard.Not g => !evalGuard g state
  | Guard.HasRole role =>
    match state.user with
    | Role.User id => role == id
    | Role.Service name => role == name
    | Role.System level => role == "system"
    | Role.Tenant name => role == name
    | Role.Group name => role == name
  | Guard.HasAttribute key value =>
    state.attributes.any (fun attr =>
      match attr with
      | Attribute.String k v => k == key && v == value
      | _ => false)
  | Guard.SessionAttribute key value =>
    state.session.attributes.any (fun attr =>
      match attr with
      | Attribute.String k v => k == key && v == value
      | _ => false)
  | Guard.EpochIn range =>
    state.timestamp >= range.start && state.timestamp <= range.end
  | Guard.ScopeMatch scope =>
    state.scope.tenant == scope.tenant &&
    state.scope.project == scope.project &&
    state.scope.environment == scope.environment
  | Guard.StringEquals left right => left == right
  | Guard.StringContains haystack needle => haystack.contains needle
  | Guard.NumberEquals left right => left == right
  | Guard.NumberLessThan left right => left < right
  | Guard.NumberGreaterThan left right => left > right
  -- New ABAC primitives
  | Guard.Attr key =>
    state.attributes.any (fun attr =>
      match attr with
      | Attribute.String k _ => k == key
      | _ => false)
  | Guard.Session key =>
    state.session.attributes.any (fun attr =>
      match attr with
      | Attribute.String k _ => k == key
      | _ => false)
  | Guard.EpochInRange start end =>
    state.timestamp >= start && state.timestamp <= end
  | Guard.Scope tenant =>
    state.scope.tenant == tenant

/-- Check if an action is allowed by a policy -/
def isAllowed (policy : PolicyRule) (state : State) (event : Event) : Bool :=
  policy.clauses.any (fun clause =>
    match clause.action with
    | "allow" =>
      eventMatches clause.operation event &&
      evalGuard clause.guard state
    | "forbid" =>
      eventMatches clause.operation event &&
      evalGuard clause.guard state
    | _ => false)

/-- Check if events match (simplified matching) -/
def eventMatches (expected : Event) (actual : Event) : Bool :=
  match expected, actual with
  | Event.Call role1 tool1, Event.Call role2 tool2 =>
    role1 == role2 && tool1 == tool2
  | Event.Read role1 doc1 path1, Event.Read role2 doc2 path2 =>
    role1 == role2 && doc1 == doc2 && path1 == path2
  | Event.Write role1 doc1 path1, Event.Write role2 doc2 path2 =>
    role1 == role2 && doc1 == doc2 && path1 == path2
  | Event.Log msg1 level1, Event.Log msg2 level2 =>
    msg1 == msg2 && level1 == level2
  | Event.Declassify from1 to1, Event.Declassify from2 to2 =>
    from1 == from2 && to1 == to2
  | Event.Emit type1 payload1, Event.Emit type2 payload2 =>
    type1 == type2 && payload1 == payload2
  | Event.Retrieve path1 hash1, Event.Retrieve path2 hash2 =>
    path1 == path2 && hash1 == hash2
  | _, _ => false

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

/-- Example policy rules with read/write events and ABAC guards -/
def examplePolicy : PolicyRule :=
  { name := "email-policy"
    description := "Allow email sending for authorized users"
    clauses := [
      { action := "allow"
        role := Role.User "email_user"
        operation := Event.Call (Role.User "email_user") (Tool.Email "user@example.com" "Test")
        guard := Guard.And
          (Guard.HasRole "email_user")
          (Guard.ScopeMatch { tenant := "tenantA", project := "email", environment := "prod" })
      }
    ]
    priority := 1
  }

def readPolicy : PolicyRule :=
  { name := "document-read-policy"
    description := "Allow document reading with proper permissions"
    clauses := [
      { action := "allow"
        role := Role.User "reader"
        operation := Event.Read (Role.User "reader") { id := "doc1", path := ["field1"], version := 1 } ["field1"]
        guard := Guard.And
          (Guard.HasRole "reader")
          (Guard.EpochIn { start := 0, end := 9999999999 })
      }
    ]
    priority := 2
  }

def writePolicy : PolicyRule :=
  { name := "document-write-policy"
    description := "Allow document writing with proper permissions"
    clauses := [
      { action := "forbid"
        role := Role.User "reader"
        operation := Event.Write (Role.User "reader") { id := "doc1", path := ["field1"], version := 1 } ["field1"]
        guard := Guard.True
      },
      { action := "allow"
        role := Role.User "writer"
        operation := Event.Write (Role.User "writer") { id := "doc1", path := ["field1"], version := 1 } ["field1"]
        guard := Guard.And
          (Guard.HasRole "writer")
          (Guard.ScopeMatch { tenant := "tenantA", project := "docs", environment := "prod" })
      }
    ]
    priority := 3
  }

-- New DSL rules with ABAC primitives
def abacReadPolicy : DSLRule :=
  { name := "abac-read-policy"
    description := "ABAC-based document reading with attr/session/epoch/scope guards"
    allow_call := none
    allow_read := some (Role.User "data_scientist", { id := "dataset1", path := ["sensitive"], version := 1 }, ["sensitive"],
      Guard.And
        (Guard.Attr "project")
        (Guard.And
          (Guard.Session "approved")
          (Guard.And
            (Guard.EpochInRange 1000 2000)
            (Guard.Scope "tenantA"))))
    forbid_write := none
    clauses := []
    priority := 4
  }

def abacWritePolicy : DSLRule :=
  { name := "abac-write-policy"
    description := "ABAC-based document writing with comprehensive guards"
    allow_call := none
    allow_read := none
    forbid_write := some (Role.User "guest", { id := "config", path := ["admin"], version := 1 }, ["admin"],
      Guard.Or
        (Guard.Not (Guard.Attr "admin_access"))
        (Guard.Not (Guard.Scope "tenantA")))
    clauses := []
    priority := 5
  }

end PF.ActionDSL
