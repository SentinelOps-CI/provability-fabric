import Lake
open Lake DSL

package spec {
  -- add package configuration options here
}

@[default_target]
lean_lib Spec {
  -- add library configuration options here
}

-- Use vendored mathlib instead of fetching from git
require mathlib from "../../../vendor/mathlib"
