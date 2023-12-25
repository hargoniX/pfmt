import Lake
open Lake DSL

package «pfmt» {
  -- add package configuration options here
}

lean_lib «Pfmt» {
  -- add library configuration options here
}

@[default_target]
lean_exe «pfmt» {
  root := `Main
}
