import Lake

open Lake DSL

package love

@[default_target]
lean_lib LoVe {
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]
}

@[default_target]
lean_lib ChessWidget

require mathlib from git "https://github.com/leanprover-community/mathlib4"
-- require metaExamples from git "https://github.com/siddhartha-gadgil/MetaExamples.git" @ "main"
