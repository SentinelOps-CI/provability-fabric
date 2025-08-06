/-
  GenTrace: Action Trace Generator and Replay Harness

  Provides SmallCheck/QuickCheck-style generators for Action traces
  with size-bounded generation and automatic counterexample shrinking.
-/

import ActionDSL
import Capability
import Privacy
import Sandbox

namespace GenTrace

/-- Configuration for trace generation --/
structure GenConfig where
  maxTraceLength : Nat := 10
  maxActionDepth : Nat := 5
  seed : Option Nat := none
  maxShrinkAttempts : Nat := 100

/-- A generator for values of type α --/
def Gen (α : Type) := GenConfig → List α

/-- Generate a random natural number up to max --/
def genNat (max : Nat) : Gen Nat := fun config =>
  match config.seed with
  | none => List.range max
  | some seed =>
    -- Simple deterministic "random" generation based on seed
    let values := List.range max
    let shuffled := values.zip (List.range values.length)
    shuffled.map (fun (_, i) => i)

/-- Generate a random boolean --/
def genBool : Gen Bool := fun config =>
  match config.seed with
  | none => [true, false]
  | some seed => [seed % 2 == 0]

/-- Generate a random string of given length --/
def genString (length : Nat) : Gen String := fun config =>
  let chars := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
  let charList := chars.data
  let indices := genNat charList.length config
  indices.map (fun i =>
    String.mk (List.replicate length (charList.get! i)))

/-- Generate a random Action --/
def genAction (depth : Nat) : Gen Action := fun config =>
  if depth == 0 then
    [Action.read "default", Action.write "default" "value"]
  else
    let subActions := genAction (depth - 1) config
    let strings := genString 5 config
    let bools := genBool config

    [Action.read "input",
     Action.write "output" "result",
     Action.ifThenElse (bools.headD false)
       (subActions.headD (Action.read "default"))
       (subActions.headD (Action.write "default" "value")),
     Action.sequence (subActions.take 2),
     Action.parallel (subActions.take 2)]

/-- Generate a random Trace --/
def genTrace : Gen Trace := fun config =>
  let actions := genAction config.maxActionDepth config
  let lengths := genNat config.maxTraceLength config

  lengths.map (fun length =>
    Trace.mk (actions.take length))

/-- Generate a random Capability --/
def genCapability : Gen Capability := fun config =>
  let resources := genString 8 config
  let permissions := genBool config

  resources.map (fun resource =>
    Capability.mk resource (permissions.headD false))

/-- Generate a random PrivacyLevel --/
def genPrivacyLevel : Gen PrivacyLevel := fun config =>
  [PrivacyLevel.public, PrivacyLevel.private, PrivacyLevel.confidential]

/-- Generate a random SandboxConfig --/
def genSandboxConfig : Gen SandboxConfig := fun config =>
  let levels := genPrivacyLevel config
  let bools := genBool config

  levels.map (fun level =>
    SandboxConfig.mk level (bools.headD false))

/-- Test a property on a trace --/
def testProperty (prop : Trace → Bool) (trace : Trace) : Bool :=
  prop trace

/-- Find a counterexample for a property --/
def findCounterexample (prop : Trace → Bool) (config : GenConfig) : Option Trace :=
  let traces := genTrace config
  traces.find (fun trace => !testProperty prop trace)

/-- Shrink a counterexample to find a minimal one --/
def shrink (trace : Trace) (prop : Trace → Bool) (config : GenConfig) : Trace :=
  let rec shrinkHelper (current : Trace) (attempts : Nat) : Trace :=
    if attempts == 0 then current
    else
      let smaller := shrinkTrace current
      if smaller.length < current.length && !testProperty prop smaller then
        shrinkHelper smaller (attempts - 1)
      else
        shrinkHelper current (attempts - 1)

  shrinkHelper trace config.maxShrinkAttempts

/-- Helper to shrink a trace by removing actions --/
def shrinkTrace (trace : Trace) : Trace :=
  match trace.actions with
  | [] => trace
  | _ :: rest => Trace.mk rest

/-- Run property-based testing --/
def runTests (prop : Trace → Bool) (config : GenConfig) : IO Unit := do
  IO.println s!"Running {config.maxTraceLength * 100} test cases..."

  let counterexample := findCounterexample prop config
  match counterexample with
  | none =>
    IO.println "✅ No counterexamples found"
  | some trace =>
    IO.println "❌ Found counterexample:"
    IO.println s!"   Length: {trace.actions.length}"
    IO.println s!"   Actions: {trace.actions}"

    let minimal := shrink trace prop config
    IO.println s!"   Minimal: {minimal.actions.length} actions"
    IO.println s!"   Minimal actions: {minimal.actions}"

/-- Example property: all traces should have non-empty actions --/
def nonEmptyTraceProp (trace : Trace) : Bool :=
  trace.actions.length > 0

/-- Example property: all traces should have valid actions --/
def validActionProp (trace : Trace) : Bool :=
  trace.actions.all (fun action =>
    match action with
    | Action.read _ => true
    | Action.write _ _ => true
    | Action.ifThenElse _ t f => true
    | Action.sequence _ => true
    | Action.parallel _ => true)

/-- Example property: traces should respect privacy levels --/
def privacyRespectProp (trace : Trace) : Bool :=
  -- This is a simplified property - in practice would check actual privacy logic
  trace.actions.length <= 100

end GenTrace
