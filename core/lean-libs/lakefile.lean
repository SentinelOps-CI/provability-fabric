import Lake
open Lake DSL

package Fabric {
  -- add package configuration options here
}

@[default_target]
lean_lib ActionDSL {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "2025-07-15-abe123"
