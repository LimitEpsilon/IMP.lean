import Lake
open Lake DSL

package «test».«lean» where
  -- add package configuration options here

lean_lib «Test».«Lean» where
  -- add library configuration options here

@[default_target]
lean_exe «test-lean» where
  supportInterpreter := true
  root := `Main
