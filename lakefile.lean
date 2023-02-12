import Lake
open Lake DSL

package Simpl {
  -- add package configuration options here
}

lean_lib Simpl {
  -- add library configuration options here
}

@[default_target]
lean_exe test {
  root := `Main
}

 require std from git "https://github.com/leanprover/std4.git" @ "main"
