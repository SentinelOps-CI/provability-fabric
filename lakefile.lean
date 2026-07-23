import Lake
open Lake DSL

package provability_fabric {
  -- add package configuration options here
}

@[default_target]
lean_lib Fabric {
  -- Root package marker. Canonical Policy lives in proofs/Policy.lean (proofs lake package).
  roots := #[`Fabric]
}

-- Use vendored mathlib instead of fetching from git
require mathlib from "vendor/mathlib"
