import Lake
open Lake DSL

package «flypitch» where
  -- add package configuration options here

lean_lib «Flypitch» where
  -- add library configuration options here

@[default_target]
lean_exe «flypitch» where
  root := `Main
