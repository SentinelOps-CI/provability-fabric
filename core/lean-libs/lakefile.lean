import Lake
open Lake DSL

package Fabric {
  -- add package configuration options here
}

@[default_target]
lean_lib ActionDSL {
  roots := #[`ActionDSL, `ActionDSL.Safety]
  -- add library configuration options here
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

-- ExportDFA executable
lean_exe ExportDFA {
  root := `ExportDFA
  supportInterpreter := true
}

-- Use vendored mathlib instead of fetching from git
require mathlib from "../../../vendor/mathlib"
