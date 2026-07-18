import Lake
open Lake DSL

package Fabric {
  -- add package configuration options here
}

@[default_target]
lean_lib ActionDSL {
  roots := #[`ActionDSL, `ActionDSL.Safety]
}

/-- Runtime micro-interpreter + ActionDSL↔DFA coupling (F33 / P4). -/
lean_lib Runtime {
  roots := #[`Runtime.MicroInterp]
}

lean_lib Budget {
  roots := #[`Budget]
}

lean_lib Fabric {
  roots := #[`Fabric]
}

lean_lib Capability {
  -- add library configuration options here
}

lean_lib Redaction {
  -- add library configuration options here
}

lean_lib Privacy {
  -- add library configuration options here
}

lean_lib Sandbox {
  -- add library configuration options here
}

lean_lib GenTrace {
  -- add library configuration options here
}

lean_lib Invariants {
  roots := #[`Invariants]
}

-- ExportDFA executable
lean_exe ExportDFA {
  root := `ExportDFA
}

-- Use vendored mathlib instead of fetching from git
require mathlib from "../../vendor/mathlib"
