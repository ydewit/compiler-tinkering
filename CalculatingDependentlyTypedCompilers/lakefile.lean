import Lake
open Lake DSL

package "CalculatingDependentlyTypedCompilers" where
  -- add package configuration options here

lean_lib «CalculatingDependentlyTypedCompilers» where
  -- add library configuration options here

@[default_target]
lean_exe "calculatingdependentlytypedcompilers" where
  root := `Main
