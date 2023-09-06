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

require std from git
  "https://github.com/leanprover/std4" @ "d5471b83378e8ace4845f9a029af92f8b0cf10cb"
