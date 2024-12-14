import Lean
set_option linter.unusedVariables false
-- import Lean.PrettyPrinter.Delaborator.SubExpr

-- open Lean.SubExpr

/-
a maze looks like:
╔═══════╗
║▓▓▓▓▓▓▓║
-- 007new:
║▓░▓@▓░▓║
║▓░▓░░░▓║
║▓░░▓░▓▓║
║▓▓░▓░▓▓║
║▓░░░░▓▓║
║▓░▓▓▓▓▓║
╚═══════╝
-/

declare_syntax_cat game_cell
declare_syntax_cat game_cell_sequence
declare_syntax_cat game_row
-- 007new:
declare_syntax_cat horizontal_border
declare_syntax_cat game_top_row
declare_syntax_cat game_bottom_row

-- 007new:
syntax "═" : horizontal_border

-- 009new:
syntax "\n╔" horizontal_border* "╗\n" : game_top_row

syntax "╚" horizontal_border* "╝\n" : game_bottom_row


syntax "░" : game_cell
syntax "▓" : game_cell
syntax "@" : game_cell

-- syntax game_cell'* : game_c -- 这里打错了吗？不能运行
-- 007new:
syntax "║" game_cell* "║\n" : game_row
syntax game_top_row game_row* game_bottom_row : term

-- 008new:
syntax "╣{" game_row* "}╠" : term
syntax "╣" game_cell* "╠" : term
-- x is column number
-- y is row number
-- upper left is ⟨0,0⟩


structure Coords where
  x : Nat
  y : Nat

structure GameState where
-- 007new:
  size : Coords
  position : Coords
  walls: List Coords

-- 007new:
inductive CellContents where
  | empty  : CellContents
  | wall  : CellContents
  | player : CellContents

-- 013new:
def update_state_with_row_aux : Nat → Nat → List CellContents → GameState → GameState
| currentRowNum, currentColNum, [], oldState => oldState
| currentRowNum, currentColNum, cell::contents, oldState =>
             let oldState' := update_state_with_row_aux currentRowNum (currentColNum+1) contents oldState
             match cell with
             | CellContents.empty => oldState'
             | CellContents.wall => {size     := oldState'.size,
                                     position := oldState'.position,
                                     walls    := ⟨currentColNum,currentRowNum⟩::oldState'.walls}
             | CellContents.player => {size     := oldState'.size,
                                       position := ⟨currentColNum,currentRowNum⟩,
                                       walls    := oldState'.walls}
def update_state_with_row : Nat → List CellContents → GameState → GameState
| currentRowNum, rowContents, oldState => update_state_with_row_aux currentRowNum 0 rowContents oldState
-- size, current row, remaining cells -> gamestatem
def game_state_from_cells_aux : Coords → Nat → List (List CellContents) → GameState
| size, _, [] => ⟨size, ⟨0,0⟩, []⟩
| size, currentRow, row::rows =>
        let prevState := game_state_from_cells_aux size (currentRow + 1) rows
        update_state_with_row currentRow row prevState
-- size, remaining cells -> gamestatem


-- 013new:
def game_state_from_cells : Coords → List (List CellContents) → GameState
| size, cells => game_state_from_cells_aux size 0 cells


macro_rules
| `(╣╠) => `(([] : List CellContents))
| `(╣░ $cells:game_cell*╠) => `(CellContents.empty :: ╣$cells:game_cell*╠)
| `(╣▓ $cells:game_cell*╠) => `(CellContents.wall :: ╣$cells:game_cell*╠)
| `(╣@ $cells:game_cell*╠) => `(CellContents.player :: ╣$cells:game_cell*╠)
macro_rules
| `(╣{}╠) => `(([] : List (List CellContents)))
| `(╣{ ║$cells:game_cell*║  $rows:game_row*}╠) => `(╣$cells:game_cell*╠ :: ╣{$rows:game_row*}╠)


-- 007new:
macro_rules
| `(╔ $tb:horizontal_border* ╗
    $rows:game_row*                   -- 它这里怎么知道是识别若干行的呢？
    ╚ $bb:horizontal_border* ╝) =>
-- 009new:
    let rsize := Lean.Syntax.mkNumLit (toString rows.size) -- there's gotta be a better way to do this
    let csize := Lean.Syntax.mkNumLit (toString tb.size) -- there's gotta be a better way to do this
    `( game_state_from_cells ⟨$csize,$rsize⟩ ╣{$rows:game_row*}╠ )

-- 013new:
-- #check Array.size
#reduce ╔═══════╗ -- 终于可以数清楚迷宫的面积，但是位置是不是不对呢？
        ║▓▓▓▓▓▓▓║
        ║▓░▓@▓░▓║
        ║▓░▓░░░▓║
        ║▓░░▓░▓▓║
        ║▓▓░▓░▓▓║
        ║▓░░░░▓▓║
        ║▓░▓▓▓▓▓║
        ╚═══════╝

def extractXY : Lean.Expr → Lean.PrettyPrinter.Delaborator.DelabM (Nat × Nat)
| e => do
  let e':Lean.Expr ← (Lean.Meta.whnf e)
  let sizeArgs := Lean.Expr.getAppArgs e'
  let numCols := (Lean.Expr.natLit? sizeArgs[0]!).get!
  let numRows := (Lean.Expr.natLit? sizeArgs[1]!).get!
  return (numCols, numRows) -- 我自己加了个return



@[delab app.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  guard $ e.getAppNumArgs == 3
-- 014new:
    -- let pexpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
  let sizeExpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
-- 014new:
  let (numCols, numRows) ← extractXY sizeExpr
  let positionExpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  let (playerCol, playerRow) ← extractXY positionExpr
  dbg_trace (playerCol, playerRow)

  -- 011new:
  let topBarCell ← `(horizontal_border| ═)
  let topBar := Array.mkArray numCols topBarCell
  -- 014new:
  let playerCell ← `(game_cell| @) -- 没有提取成功玩家位置啊？

  let emptyCell ← `(game_cell| ░)
  let emptyRow := Array.mkArray numCols emptyCell
  let emptyRowStx ← `(game_row|║$emptyRow:game_cell*║)
  let allRows := Array.mkArray numRows emptyRowStx
  `(╔$topBar:horizontal_border*╗
    $allRows:game_row*
    ╚$topBar:horizontal_border*╝)


#reduce ╔═══════╗ -- 打印了一个空地图？它是不是在尝试读出来，然后打印在infoview
        ║▓▓▓▓▓▓▓║
        ║▓░▓@▓░▓║
        ║▓░▓░░░▓║
        ║▓░░▓░▓▓║
        ║▓▓░▓░▓▓║
        ║▓░░░░▓▓║
        ║▓░▓▓▓▓▓║
        ╚═══════╝
