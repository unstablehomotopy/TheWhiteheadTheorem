import Lake
open Lake DSL

package «threeWhiteheadTheoremsandThreePuppeSequences» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_lib «ThreeWhiteheadTheoremsandThreePuppeSequences» {
  -- add any library configuration options here
}
