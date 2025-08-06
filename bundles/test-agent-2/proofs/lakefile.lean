import Lake
open Lake DSL

package spec {
  -- add package configuration options here
}

@[default_target]
lean_lib Spec {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.7.0"
