import Lake
open Lake DSL

package ART {
  -- add package configuration options here
}

@[default_target]
lean_lib Spec {
  -- add library configuration options here
}

require mathlib from "../../../../vendor/mathlib"
