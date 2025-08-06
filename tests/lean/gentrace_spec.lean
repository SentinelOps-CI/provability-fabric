/-
  GenTrace Specification Tests

  Tests for the trace generator and replay harness functionality.
-/

import GenTrace
import ActionDSL
import Capability
import Privacy
import Sandbox

namespace GenTraceSpec

/-- Test that trace generation produces valid traces --/
def testTraceGeneration : IO Unit := do
  IO.println "🧪 Testing trace generation..."

  let config := GenConfig.mk 5 3 none 50
  let traces := GenTrace.genTrace config

  IO.println s!"Generated {traces.length} traces"

  for trace in traces do
    IO.println s!"  Trace length: {trace.actions.length}"
    IO.println s!"  Actions: {trace.actions}"

/-- Test that shrinking produces smaller counterexamples --/
def testShrinking : IO Unit := do
  IO.println "🔍 Testing counterexample shrinking..."

  let config := GenConfig.mk 10 5 none 100

  -- Create a property that fails for long traces
  let longTraceProp (trace : Trace) : Bool :=
    trace.actions.length <= 5

  let traces := GenTrace.genTrace config
  let longTrace := traces.find (fun t => t.actions.length > 5)

  match longTrace with
  | none => IO.println "No long traces found for testing"
  | some trace =>
    IO.println s!"Original trace length: {trace.actions.length}"
    let shrunk := GenTrace.shrink trace longTraceProp config
    IO.println s!"Shrunk trace length: {shrunk.actions.length}"
    IO.println s!"Shrunk actions: {shrunk.actions}"

/-- Test that seeded generation is reproducible --/
def testSeededGeneration : IO Unit := do
  IO.println "🌱 Testing seeded generation..."

  let config1 := GenConfig.mk 5 3 (some 42) 50
  let config2 := GenConfig.mk 5 3 (some 42) 50

  let traces1 := GenTrace.genTrace config1
  let traces2 := GenTrace.genTrace config2

  IO.println s!"Seeded generation 1: {traces1.length} traces"
  IO.println s!"Seeded generation 2: {traces2.length} traces"

  if traces1 == traces2 then
    IO.println "✅ Seeded generation is reproducible"
  else
    IO.println "❌ Seeded generation is not reproducible"

/-- Test property-based testing framework --/
def testPropertyBasedTesting : IO Unit := do
  IO.println "🎯 Testing property-based testing..."

  let config := GenConfig.mk 8 4 none 50

  -- Test a property that should always pass
  let alwaysTrueProp (trace : Trace) : Bool := true
  IO.println "Testing always-true property..."
  GenTrace.runTests alwaysTrueProp config

  -- Test a property that should sometimes fail
  let lengthProp (trace : Trace) : Bool := trace.actions.length <= 3
  IO.println "Testing length property..."
  GenTrace.runTests lengthProp config

/-- Test capability generation --/
def testCapabilityGeneration : IO Unit := do
  IO.println "🔐 Testing capability generation..."

  let config := GenConfig.mk 5 3 none 50
  let capabilities := GenTrace.genCapability config

  IO.println s!"Generated {capabilities.length} capabilities"

  for cap in capabilities.take 5 do
    IO.println s!"  Capability: {cap.resource} -> {cap.hasPermission}"

/-- Test privacy level generation --/
def testPrivacyGeneration : IO Unit := do
  IO.println "🔒 Testing privacy level generation..."

  let config := GenConfig.mk 5 3 none 50
  let levels := GenTrace.genPrivacyLevel config

  IO.println s!"Generated {levels.length} privacy levels"

  for level in levels do
    IO.println s!"  Privacy level: {level}"

/-- Test sandbox config generation --/
def testSandboxGeneration : IO Unit := do
  IO.println "🏖️ Testing sandbox config generation..."

  let config := GenConfig.mk 5 3 none 50
  let sandboxes := GenTrace.genSandboxConfig config

  IO.println s!"Generated {sandboxes.length} sandbox configs"

  for sandbox in sandboxes.take 5 do
    IO.println s!"  Sandbox: {sandbox.level} -> {sandbox.isIsolated}"

/-- Main test runner --/
def main : IO Unit := do
  IO.println "🚀 Running GenTrace specification tests"
  IO.println "=" * 50

  testTraceGeneration
  IO.println ""

  testShrinking
  IO.println ""

  testSeededGeneration
  IO.println ""

  testPropertyBasedTesting
  IO.println ""

  testCapabilityGeneration
  IO.println ""

  testPrivacyGeneration
  IO.println ""

  testSandboxGeneration
  IO.println ""

  IO.println "✅ All GenTrace tests completed"

end GenTraceSpec
