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
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

namespace Fabric

/-- System call types that can be made by WASM modules -/
inductive Sys where
  | FileOpen (path : String)
  | FileRead (fd : Nat)
  | FileWrite (fd : Nat)
  | NetworkConnect (host : String) (port : Nat)
  | NetworkSend (fd : Nat)
  | NetworkRecv (fd : Nat)
  | ProcessSpawn (cmd : String)
  | MemoryAlloc (size : Nat)
  | MemoryFree (ptr : Nat)

/-- Check if a system call is allowed -/
def AllowedSyscall : Sys → Prop
  | Sys.FileOpen _ => False  -- No file operations allowed
  | Sys.FileRead _ => False
  | Sys.FileWrite _ => False
  | Sys.NetworkConnect _ _ => False  -- No network operations allowed
  | Sys.NetworkSend _ => False
  | Sys.NetworkRecv _ => False
  | Sys.ProcessSpawn _ => False  -- No process spawning allowed
  | Sys.MemoryAlloc _ => True   -- Memory allocation is allowed
  | Sys.MemoryFree _ => True    -- Memory deallocation is allowed

/-- Get the system calls made by an action -/
def syscall_trace : Action → List Sys
  | Action.SendEmail _ => []  -- Email actions don't make syscalls
  | Action.LogSpend _ => []   -- Spend actions don't make syscalls

/-- Check if all syscalls in a trace are allowed -/
def syscall_trace_allowed : List Sys → Prop
  | [] => True
  | (s :: rest) => AllowedSyscall s ∧ syscall_trace_allowed rest

/-- Theorem: WASM capabilities are respected -/
theorem thm_wasm_caps :
  ∀ (a : Action), (∀ (s : Sys), s ∈ syscall_trace a → AllowedSyscall s) := by
  intro a
  cases a with
  | SendEmail score =>
    simp [syscall_trace]
    intro s h_mem
    -- Empty list has no elements
    contradiction
  | LogSpend usd =>
    simp [syscall_trace]
    intro s h_mem
    -- Empty list has no elements
    contradiction

/-- Check if a trace has no network syscalls -/
def no_net_syscalls : List Action → Prop
  | [] => True
  | (a :: rest) =>
    (∀ (s : Sys), s ∈ syscall_trace a → ¬ s.isNetworkCall) ∧
    no_net_syscalls rest
  where
    isNetworkCall : Sys → Prop
      | Sys.NetworkConnect _ _ => True
      | Sys.NetworkSend _ => True
      | Sys.NetworkRecv _ => True
      | _ => False

/-- Theorem: network silence is preserved -/
theorem thm_network_silence :
  ∀ (tr : List Action), (∀ (a : Action), a ∈ tr → (∀ (s : Sys), s ∈ syscall_trace a → AllowedSyscall s)) → no_net_syscalls tr := by
  intro tr h_allowed
  induction tr with
  | nil =>
    simp [no_net_syscalls]
  | cons head tail ih =>
    simp [no_net_syscalls]
    constructor
    · -- Prove ∀ (s : Sys), s ∈ syscall_trace head → ¬ s.isNetworkCall
      intro s h_mem
      have h_allowed_head := h_allowed head (List.mem_cons_self head tail)
      have h_allowed_s := h_allowed_head s h_mem
      -- If s is allowed, it's not a network call (since network calls are forbidden)
      cases s with
      | NetworkConnect _ _ => contradiction
      | NetworkSend _ => contradiction
      | NetworkRecv _ => contradiction
      | _ => simp [AllowedSyscall.isNetworkCall]
    · -- Prove no_net_syscalls tail
      have h_allowed_tail := λ a h_mem => h_allowed a (List.mem_cons_of_mem head h_mem)
      exact ih h_allowed_tail

/-- WASI capability model -/
inductive WASICap where
  | FileRead (path : String)
  | FileWrite (path : String)
  | Network (host : String)
  | Process (cmd : String)
  | Memory

/-- Check if a WASI capability is allowed -/
def AllowedWASICap : WASICap → Prop
  | WASICap.FileRead _ => False  -- No file access
  | WASICap.FileWrite _ => False
  | WASICap.Network _ => False   -- No network access
  | WASICap.Process _ => False   -- No process access
  | WASICap.Memory => True       -- Memory access allowed

/-- Map system calls to WASI capabilities -/
def syscall_to_wasi : Sys → Option WASICap
  | Sys.FileOpen path => some (WASICap.FileRead path)
  | Sys.FileRead _ => some WASICap.Memory
  | Sys.FileWrite _ => some WASICap.Memory
  | Sys.NetworkConnect host _ => some (WASICap.Network host)
  | Sys.NetworkSend _ => some (WASICap.Network "")
  | Sys.NetworkRecv _ => some (WASICap.Network "")
  | Sys.ProcessSpawn cmd => some (WASICap.Process cmd)
  | Sys.MemoryAlloc _ => some WASICap.Memory
  | Sys.MemoryFree _ => some WASICap.Memory

/-- Check if a system call respects WASI capabilities -/
def syscall_respects_wasi : Sys → Prop
  | s =>
    match syscall_to_wasi s with
    | none => True
    | some cap => AllowedWASICap cap

/-- Theorem: system calls respect WASI capabilities -/
theorem thm_syscall_respects_wasi :
  ∀ (s : Sys), AllowedSyscall s → syscall_respects_wasi s := by
  intro s h_allowed
  cases s with
  | FileOpen path =>
    simp [AllowedSyscall] at h_allowed
    contradiction
  | FileRead fd =>
    simp [AllowedSyscall] at h_allowed
    contradiction
  | FileWrite fd =>
    simp [AllowedSyscall] at h_allowed
    contradiction
  | NetworkConnect host port =>
    simp [AllowedSyscall] at h_allowed
    contradiction
  | NetworkSend fd =>
    simp [AllowedSyscall] at h_allowed
    contradiction
  | NetworkRecv fd =>
    simp [AllowedSyscall] at h_allowed
    contradiction
  | ProcessSpawn cmd =>
    simp [AllowedSyscall] at h_allowed
    contradiction
  | MemoryAlloc size =>
    simp [AllowedSyscall, syscall_respects_wasi, syscall_to_wasi, AllowedWASICap] at h_allowed
  | MemoryFree ptr =>
    simp [AllowedSyscall, syscall_respects_wasi, syscall_to_wasi, AllowedWASICap] at h_allowed

/-- Adapter witness function type -/
def AdapterWitness := Action → List Sys

/-- Check if an adapter witness is valid -/
def valid_adapter_witness (witness : AdapterWitness) : Prop :=
  ∀ (a : Action), ∀ (s : Sys), s ∈ witness a → AllowedSyscall s

/-- Example adapter witness for hello-world -/
def hello_world_witness : AdapterWitness
  | Action.SendEmail _ => []
  | Action.LogSpend _ => []

/-- Theorem: hello-world adapter witness is valid -/
theorem thm_hello_world_witness_valid :
  valid_adapter_witness hello_world_witness := by
  intro a s h_mem
  cases a with
  | SendEmail score =>
    simp [hello_world_witness] at h_mem
    contradiction
  | LogSpend usd =>
    simp [hello_world_witness] at h_mem
    contradiction

/-- Check if an adapter is sandbox-safe -/
def adapter_sandbox_safe (witness : AdapterWitness) : Prop :=
  valid_adapter_witness witness ∧
  (∀ (a : Action), syscall_trace a = witness a)

/-- Theorem: hello-world adapter is sandbox-safe -/
theorem thm_hello_world_sandbox_safe :
  adapter_sandbox_safe hello_world_witness := by
  constructor
  · exact thm_hello_world_witness_valid
  · intro a
    cases a with
    | SendEmail score =>
      simp [syscall_trace, hello_world_witness]
    | LogSpend usd =>
      simp [syscall_trace, hello_world_witness]

end Fabric
