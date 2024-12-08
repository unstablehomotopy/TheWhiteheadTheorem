import Lake
open Lake DSL

package «threeWhiteheadTheoremsandThreePuppeSequences» {
  -- add any package configuration options here

  --   moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib", -- LeanCopilot
  --   "-lctranslate2"                                   -- LeanCopilot
  -- ]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- require batteries from git
--   "https://github.com/leanprover-community/batteries" @ "main"

-- require LeanCopilot from git  -- LeanCopilot
--   "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.4.1"

@[default_target]
lean_lib «CWComplex/CWComplex» {
  -- add any library configuration options here
}
