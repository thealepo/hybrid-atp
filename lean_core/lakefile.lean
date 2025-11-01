import Lake
open Lake DSL

package «hybrid_atp» where
  -- can specify Lean version
  -- leanOptions := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib HybridAtp