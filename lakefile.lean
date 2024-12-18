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

@[default_target]
lean_lib Sudoku {
  roots := #[`Sudoku]
  globs := #[Glob.submodules `Sudoku]
}

@[default_target]
lean_lib LeanSudoku {
  roots := #[`LeanSudoku]
  globs := #[Glob.submodules `LeanSudoku]
}



require mathlib from git "https://github.com/leanprover-community/mathlib4"
-- require metaExamples from git "https://github.com/siddhartha-gadgil/MetaExamples.git" @ "main"
