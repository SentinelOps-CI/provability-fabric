import Lake
open Lake DSL

package provability_fabric {
  -- add package configuration options here
}

@[default_target]
lean_lib Fabric {
  -- add library configuration options here
  roots := #[`Fabric, `Policy]
}

-- Use vendored mathlib instead of fetching from git
require mathlib from "vendor/mathlib"

@[default_target]
lean_exe proofbench {
  root := `ProofBench
}
