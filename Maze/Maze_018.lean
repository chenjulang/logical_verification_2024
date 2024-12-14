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
-- 016new:
deriving BEq

-- 015new:
instance : ToString Coords where
  toString := (λ ⟨x,y⟩ => String.join ["Coords.mk ", toString x, ", ", toString y])

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

-- 015new:
def extractXY : Lean.Expr → Lean.PrettyPrinter.Delaborator.DelabM Coords
| e => do
  let e':Lean.Expr ← (Lean.Meta.whnf e)
  let sizeArgs := Lean.Expr.getAppArgs e'
-- 015new:
  let f := Lean.Expr.getAppFn e'

  -- let numCols := (Lean.Expr.natLit? sizeArgs[0]!).get!
  -- let numRows := (Lean.Expr.natLit? sizeArgs[1]!).get!
    let x ← Lean.Meta.whnf sizeArgs[0]!
  let y ← Lean.Meta.whnf sizeArgs[1]!
  let numCols := (Lean.Expr.natLit? x).get!
  let numRows := (Lean.Expr.natLit? y).get!

  -- return (numCols, numRows) -- 我自己加了个return
-- 015new:
  return Coords.mk numCols numRows


-- 015new:
def extractWallList : Nat -> Lean.Expr → Lean.PrettyPrinter.Delaborator.DelabM (List Coords)
| 0, _ => do return [] -- recursion deptch reached. -- 这里报错了咋办？
| (depth+1), exp => do
  let exp':Lean.Expr ← (Lean.Meta.whnf exp)
  let f := Lean.Expr.getAppFn exp'
  if f.constName!.toString == "List.cons"
  then let consArgs := Lean.Expr.getAppArgs exp'
       let rest ← extractWallList depth consArgs[2]!
       let ⟨wallCol, wallRow⟩ ← extractXY consArgs[1]!
       return (Coords.mk wallCol wallRow) :: rest
  else return [] -- "List.nil"

-- def extractWallList : Lean.Expr → Lean.MetaM (List Coords)
-- | exp => do
--   let exp':Lean.Expr ← Lean.Meta.whnf exp
--   let f := Lean.Expr.getAppFn exp'
--   if f.constName!.toString == "List.cons"
--   then let consArgs := Lean.Expr.getAppArgs exp'
--        let rest ← extractWallList consArgs[2]!
--        let ⟨wallCol, wallRow⟩ ← extractXY consArgs[1]!
--        return (Coords.mk wallCol wallRow) :: rest
--   else return [] -- "List.nil"

def update2dArray {α : Type} : Array (Array α) → Coords → α → Array (Array α)
| a, ⟨x,y⟩, v =>
   Array.set! a y $ Array.set! (Array.get! a y) x v

-- 016new:
def update2dArrayMulti {α : Type} : Array (Array α) → List Coords → α → Array (Array α)
| a, [], v => a
| a, c::cs, v =>
     let a' := update2dArrayMulti a cs v
     update2dArray a' c v

-- def delabGameRow : (Array Lean.Syntax) → Lean.PrettyPrinter.Delaborator.DelabM Lean.Syntax
-- | a => do `(game_row| ║ $a:game_cell* ║) -- 报错了

def delabGameRow : Array (Lean.TSyntax `game_cell) → Lean.PrettyPrinter.Delaborator.DelabM (Lean.TSyntax `game_row)
| a => `(game_row| ║  $a:game_cell* ║ ) -- 这样子就不报错了？



@[delab app.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  -- 016new:
  let e' ← (Lean.Meta.whnf e)
  -- 017new:
  dbg_trace "e'"
  dbg_trace e'

  guard $ e'.getAppNumArgs == 3
-- 014new:
    -- let pexpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
  let sizeExpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
-- 015new:
  let ⟨numCols, numRows⟩ ← extractXY sizeExpr

  let positionExpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.SubExpr.getExpr

-- 015new:
  -- let (playerCol, playerRow) ← extractXY positionExpr
  -- dbg_trace (playerCol, playerRow)
  let playerCoords ← extractXY positionExpr
-- 017new:
  let topBarCell ← `(horizontal_border| ═)
  let topBar := Array.mkArray numCols topBarCell

  let wallsExpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  let walls':Lean.Expr ← (Lean.Meta.whnf wallsExpr)
  -- dbg_trace walls'
  let walls'' ← extractWallList 1000000 walls'
  -- dbg_trace walls''

  -- 017new:
  -- let topBarCell ← `(horizontal_border| ═)
  -- let topBar := Array.mkArray numCols topBarCell

  -- 014new:
  let playerCell ← `(game_cell| @) -- 没有提取成功玩家位置啊？

  let emptyCell ← `(game_cell| ░)
  -- 016new:
  let wallCell ← `(game_cell| ▓)
  let emptyRow := Array.mkArray numCols emptyCell
  let emptyRowStx ← `(game_row|║$emptyRow:game_cell*║)
  let allRows := Array.mkArray numRows emptyRowStx
-- 015new:
  let a0 := Array.mkArray numRows $ Array.mkArray numCols emptyCell
  let a1 := update2dArray a0 playerCoords playerCell
  -- 016new:
  let a2 := update2dArrayMulti a1 walls'' wallCell
  let aa ← Array.mapM delabGameRow a2

-- 015new:
  `(╔$topBar:horizontal_border*╗
    $aa:game_row*
    -- $allRows:game_row*
    ╚$topBar:horizontal_border*╝)


-- 016new:
def maze1 := ╔════════╗
             ║▓▓▓▓▓▓▓▓║
             ║▓░▓@▓░▓▓║
             ║▓░▓░░░▓▓║
             ║▓░░▓░▓▓▓║
             ║▓▓░▓░▓░░║
             ║▓░░░░▓░▓║
             ║▓░▓▓▓▓░▓║
             ║▓░░░░░░▓║
             ║▓▓▓▓▓▓▓▓║
             ╚════════╝
def maze2 := ╔══════╗
             ║▓▓▓▓▓▓║
             ║▓░@░░▓║
             ║▓░░░░▓║
             ║▓░░░░▓║
             ║▓▓▓▓░▓║
             ╚══════╝
-- #reduce maze2


-- 016new:
def allowed_move : GameState → GameState → Prop
| ⟨s, ⟨x,y⟩, w⟩, ⟨s', ⟨x',y'⟩, w'⟩ =>
      w = w' ∧                -- walls are static
      s = s' ∧                -- size is static
      (w.contains ⟨x',y'⟩ = false) ∧ -- not allowed to enter wall
      ((x = x' ∧ (y = y' + 1 ∨ y + 1 = y')) ∨
       (y = y' ∧ (x = x' + 1 ∨ x + 1 = x')))
def is_win : GameState → Prop
| ⟨⟨sx, sy⟩, ⟨x,y⟩, w⟩ => x = 0 ∨ y = 0 ∨ x + 1 = sx ∨ y + 1 = sy
def can_win (g : GameState) : Prop :=
  ∃ (n : Nat),
  ∃ (m : Nat → GameState),
  (g = m n) ∧
  (is_win (m 0)) ∧
  (∀ (i : Nat), i < n → allowed_move (m i) (m (i + 1)))


-- 018new:
theorem step_left
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear : w.contains ⟨x+1,y⟩ == false)
  (hclear' : w.contains ⟨x,y⟩ == false)
  (h : can_win ⟨s,⟨x,y⟩,w⟩) :
  can_win ⟨s,⟨x+1, y⟩,w⟩ :=
  let n := s.1 + 1
  ⟨n,
   λ i => sorry,
   by admit,
   by admit,
   λ i h => by admit⟩
-- 018new:
theorem step_right
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear : w.contains ⟨x,y⟩ == false)
  (hclear' : w.contains ⟨x+1,y⟩ == false)
  (h : can_win ⟨s,⟨x+1,y⟩,w⟩) :
  can_win ⟨s,⟨x, y⟩,w⟩ :=
  let n := s.1 + 1
  ⟨n,
   λ i => sorry,
   by admit,
   by admit,
   λ i h => by admit⟩
theorem step_up
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear : w.contains ⟨x,y+1⟩ == false)
  (hclear' : w.contains ⟨x,y⟩ == false)
  (h : can_win ⟨s,⟨x,y⟩,w⟩) :
  can_win ⟨s,⟨x, y+1⟩,w⟩ :=
  let n := s.1 + 1
  ⟨n,
   λ i => sorry,
   by admit,
   by admit,
   λ i h => by admit⟩
theorem step_down
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear : w.contains ⟨x,y⟩ == false)
  (hclear' : w.contains ⟨x,y+1⟩ == false)
  (h : can_win ⟨s,⟨x,y+1⟩,w⟩) :
  can_win ⟨s,⟨x, y⟩,w⟩ :=
  let n := s.1 + 1
  ⟨n,
   λ i => sorry,
   by admit,
   by admit,
   λ i h => by admit⟩

-- #reduce maze1
-- 018new:
def escape_west
  {s : Coords}
  {y: Nat}
  {w: List Coords} :
  can_win ⟨s,⟨0, y⟩,w⟩ := sorry
def escape_east
  {sy x y : Nat}
  {w: List Coords} :
  can_win ⟨⟨x+1, sy⟩,⟨x, y⟩,w⟩ := sorry
def escape_north
  {s : Coords}
  {x : Nat}
  {w: List Coords} :
  can_win ⟨s,⟨x, 0⟩,w⟩ := sorry
def escape_south
  {sx x y : Nat}
  {w: List Coords} :
  can_win ⟨⟨sx, y+1⟩,⟨x, y⟩,w⟩ := sorry

macro "west" : tactic => `(tactic |first |  apply step_left | fail "cannot step west")
  -- `(apply step_left ; rfl; rfl)
macro "east" : tactic => `(tactic |apply step_right)
macro "north" : tactic => `(tactic |apply step_up)
macro "south" : tactic => `(tactic |apply step_down)

-- example : can_win maze2 := by
--  apply step_left  -- 这里角色开始可以移动了，但是初始位置好像没事显示啊？
--  admit

example : can_win maze2 := by
  west
  south -- 这里走不了，可能是4个step_XXXX定理写错了哪个坐标+1
  -- south
  -- east
  -- east
  -- east
  -- south
  -- apply escape_south
