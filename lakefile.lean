import Lake
open Lake DSL

package controlflow {
  -- add package configuration options here
}

lean_lib ControlFlow {
  -- add library configuration options here
}

-- @[defaultTarget]
lean_exe controlflow {
  root := `Main
}

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.8.0"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"
