import Lean
set_option linter.unusedVariables false
-- import Lean.PrettyPrinter.Delaborator.SubExpr

-- open Lean.SubExpr

-- 006new:
namespace OneDimension

/-- 第0步：游戏状态 -/
structure GameState where
  position : Nat
  goal : Nat
-- 004new:
  size : Nat

-- 第1步：游戏里的格子放的什么 [start

inductive CellContents where
  | empty  : CellContents
  | player : CellContents
  | goal   : CellContents

/-- 通过游戏里的所有格子放的什么，推断出游戏当前的状态 -/
def game_state_from_cells :
List CellContents → GameState
-- 004new:
 | [] => ⟨0,0,0⟩
 | CellContents.empty::cells => let ⟨p,g,s⟩ := game_state_from_cells cells
                                ⟨p+1, g+1,s+1⟩
 | CellContents.player::cells => let ⟨p,g,s⟩ := game_state_from_cells cells
                                ⟨0, g+1, s+1⟩
 | CellContents.goal::cells =>  let ⟨p,g, s⟩ := game_state_from_cells cells
                                ⟨p+1, 0, s+1⟩

-- #reduce game_state_from_cells [CellContents.goal, CellContents.player, CellContents.empty, CellContents.empty] -- 打印：{ position := 1, goal := 0 }

-- 游戏里的格子放的什么 end]


-- 第2步：syntax语法 [start

-- 006new:
declare_syntax_cat game_cell'
-- declare_syntax_cat game_cell_sequence'

-- 006new:
syntax "★" : game_cell'
syntax "░" : game_cell'
syntax "@" : game_cell'

-- 008new:
-- syntax game_cell'* : game_cell_sequence'

-- 008new:
syntax "┤" game_cell'* "├ ": term

syntax "┤{" game_cell'* "}├": term

macro_rules
-- 002new：
| `(┤{}├) => `(([] : List CellContents))
-- 006new:
| `(┤{░ $cells:game_cell'* }├) => `( CellContents.empty :: ┤{$cells:game_cell'*}├)
| `(┤{★ $cells:game_cell'* }├) => `( CellContents.goal :: ┤{$cells:game_cell'*}├)
| `(┤{@ $cells:game_cell'* }├) => `( CellContents.player :: ┤{$cells:game_cell'*}├)

-- | `(┤├) => `( (⟨1, 3⟩ : GameState) )
-- | `(┤$cell:game_cell $cells:game_cell*├) => `( (⟨123, 999⟩ : GameState) )

-- 002new：
macro_rules
-- | `(┤$cells:game_cell*├) => `(game_state_from_cells  ┤{$cells:game_cell*}├ )
-- 006new:
| `(┤$cells:game_cell'*├) => `(game_state_from_cells  ┤{$cells:game_cell'*}├ )


-- #reduce ┤░@░★░░├

-- #check GameState.mk

-- 002new：
-- @[appUnexpander GameState]
-- def unexpandGameState : Lean.PrettyPrinter.Unexpander
--  | `({ position := $p, goal := $g}) => `(┤░@░★░░├)
  -- | `(GameState $p $g) => `(┤░@░░░░★░░├)
  -- | _              => throw ()

-- 006new:
@[delab app.OneDimension.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  -- 004new: delabGameState这个终于正常运行了
  guard $ e.getAppNumArgs == 3
  -- 005new:
  -- let p ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
  --          $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
  --          $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.delab
  let g ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.delab
  let s ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.delab
  -- 006new:
  let e ← `(game_cell'| ░)
  let player ← `(game_cell'| @)
  let goalc ← `(game_cell'| ★)
  -- 005new:
  -- let position : Nat := p.raw.isNatLit?.get!
  let pexpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  -- 008new:
  -- dbg_trace pexpr
  let position' ← (Lean.Meta.whnf pexpr)
  let position : Nat := (Lean.Expr.natLit? position').get!

  let goal : Nat := g.raw.isNatLit?.get!
  let size : Nat := s.raw.isNatLit?.get!
  let a0 := Array.mkArray size e
  let a1 := Array.set! a0 position player
  let a2 := Array.set! a1 goal goalc
  -- 008new:
  -- dbg_trace g
  -- dbg_trace s
  -- 006new:
  `(┤$a2:game_cell'*├)

-- #reduce ┤░@░★░░├



--| `(┤░░├) => `((⟨1, 3⟩ : GameState))

-- #check ┤░░░░├ -- 打印： { position := 123, goal := 999 } : GameState

-- #check ┤░░
--         ░░├ -- 打印： { position := 123, goal := 999 } : GameState

-- syntax语法 end]



def allowed_move : GameState → GameState → Prop
-- 004new:
| ⟨n, g, s⟩, ⟨m, h, t⟩ => (m + 1 = n ∧ g = h) ∨ (m = n + 1 ∧ g = h)


def is_win : GameState → Prop
-- 004new:
| ⟨n, m, _⟩ => n = m

def can_win (g : GameState) : Prop := -- 这么复杂的描述吗？
  ∃ (n : Nat),
  ∃ (m : Nat → GameState),
    (g = m n)
    ∧
    (is_win (m 0))
    ∧
    (∀ (i : Nat), i < n → allowed_move (m i) (m (i + 1)))

-- 004new:
theorem done {n s: Nat} : can_win ⟨n,n,s⟩ := sorry

-- theorem step_left {p g : Nat} (h : can_win ⟨p, g⟩) : can_win ⟨p + 1, g⟩ :=
-- 004new:
theorem step_left {p g s: Nat} (h : can_win ⟨p, g, s⟩) : can_win ⟨p + 1, g, s⟩ :=
  let n := p + 1
  ⟨n,
   λ i => sorry,
   by admit,
   by admit,
   λ i h => by admit⟩

-- 004new:
theorem step_right {p g s: Nat} (h : can_win ⟨p + 1, g, s⟩) : can_win ⟨p, g, s⟩ := sorry

-- 004new:
example : can_win {position := 11, goal := 7, size := 15} :=
by apply step_left
   apply step_left
   apply step_left
   apply step_left
   exact done

-- 004new:
example : can_win {position := 9, goal := 11, size := 15} :=
by
  -- 005new:
  -- apply step_right
  apply step_left
  apply step_right
  apply step_right
  apply step_right
  exact done

end OneDimension


-----------------------------------------------------


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


-- 008new:
def game_state_from_cells : Coords → List (List CellContents) → GameState
| size, [] => ⟨size, ⟨0,0⟩, []⟩
| size, _ => ⟨size, ⟨0,0⟩, []⟩ -- TODO
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

-- 009new:
#check Array.size
#reduce ╔═══════╗ -- 终于可以数清楚迷宫的面积，但是位置是不是不对呢？
        ║▓▓▓▓▓▓▓║
        ║▓░▓@▓░▓║
        ║▓░▓░░░▓║
        ║▓░░▓░▓▓║
        ║▓▓░▓░▓▓║
        ║▓░░░░▓▓║
        ║▓░▓▓▓▓▓║
        ╚═══════╝
@[delab app.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  guard $ e.getAppNumArgs == 3
  `(╔═════╗
    ║▓▓▓▓▓║
    ╚═════╝)


#reduce ╔═══════╗ -- 打印了什么，只有3行？
        ║▓▓▓▓▓▓▓║
        ║▓░▓@▓░▓║
        ║▓░▓░░░▓║
        ║▓░░▓░▓▓║
        ║▓▓░▓░▓▓║
        ║▓░░░░▓▓║
        ║▓░▓▓▓▓▓║
        ╚═══════╝
