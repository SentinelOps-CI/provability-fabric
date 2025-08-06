import Lake
open Lake DSL

package Fabric {
  -- add package configuration options here
}

@[default_target]
lean_lib ActionDSL {
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

-- Use vendored mathlib instead of fetching from git
require mathlib from "../../../vendor/mathlib"
