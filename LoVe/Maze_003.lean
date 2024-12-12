import Lean
-- import Lean.PrettyPrinter.Delaborator.SubExpr

-- open Lean.SubExpr



/-- 第0步：游戏状态 -/
structure GameState where
  position : Nat
  goal : Nat

-- 第1步：游戏里的格子放的什么 [start

inductive CellContents where
  | empty  : CellContents
  | player : CellContents
  | goal   : CellContents

/-- 通过游戏里的所有格子放的什么，推断出游戏当前的状态 -/
def game_state_from_cells :
List CellContents → GameState
 | [] =>
  ⟨0,0⟩
 | CellContents.empty::cells =>
  let ⟨p,g⟩ := game_state_from_cells cells
  ⟨p+1, g+1⟩
 | CellContents.player::cells =>
  let ⟨p,g⟩ := game_state_from_cells cells
  ⟨0, g+1⟩
 | CellContents.goal::cells =>
  let ⟨p,g⟩ := game_state_from_cells cells
  ⟨p+1, 0⟩
#reduce game_state_from_cells [CellContents.goal, CellContents.player, CellContents.empty, CellContents.empty] -- 打印：{ position := 1, goal := 0 }

-- 游戏里的格子放的什么 end]


-- 第2步：syntax语法 [start

declare_syntax_cat game_cell
declare_syntax_cat game_cell_sequence

syntax "★" : game_cell
syntax "░" : game_cell
syntax "@" : game_cell

syntax game_cell* : game_cell_sequence

syntax "┤" game_cell_sequence "├ ": term
syntax "┤{" game_cell_sequence "}├": term


macro_rules
-- 002new：
| `(┤{}├) => `(([] : List CellContents))
| `(┤{░ $cells:game_cell* }├) => `( CellContents.empty :: ┤{$cells:game_cell*}├)
| `(┤{★ $cells:game_cell* }├) => `( CellContents.goal :: ┤{$cells:game_cell*}├)
| `(┤{@ $cells:game_cell* }├) => `( CellContents.player :: ┤{$cells:game_cell*}├)

-- | `(┤├) => `( (⟨1, 3⟩ : GameState) )
-- | `(┤$cell:game_cell $cells:game_cell*├) => `( (⟨123, 999⟩ : GameState) )

-- 002new：
macro_rules
| `(┤$cells:game_cell*├) => `(game_state_from_cells  ┤{$cells:game_cell*}├ )

#reduce ┤░@░★░░├

#check GameState.mk

-- 002new：
-- @[appUnexpander GameState]
-- def unexpandGameState : Lean.PrettyPrinter.Unexpander
--  | `({ position := $p, goal := $g}) => `(┤░@░★░░├)
  -- | `(GameState $p $g) => `(┤░@░░░░★░░├)
  -- | _              => throw ()

-- 003new:
@[delab app.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  guard $ e.getAppNumArgs == 2
  let p ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.delab
  -- how to get an integer from p?
  let g ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.delab
  let y ← `(game_cell| ░)
  let x ← Array.mkArray g.isNatLit?.get! y

  dbg_trace p
  `(┤$x:game_cell*├) -- TODO

#reduce ┤░@░★░░├



--| `(┤░░├) => `((⟨1, 3⟩ : GameState))

-- #check ┤░░░░├ -- 打印： { position := 123, goal := 999 } : GameState

-- #check ┤░░
--         ░░├ -- 打印： { position := 123, goal := 999 } : GameState

-- syntax语法 end]



def allowed_move : GameState → GameState → Prop
| ⟨n, g⟩, ⟨m, h⟩ => (m + 1 = n ∧ g = h) ∨ (m = n + 1 ∧ g = h)  -- 看起来像是一维的游戏

def is_win : GameState → Prop
| ⟨n, m⟩ => n = m

def can_win (g : GameState) : Prop := -- 这么复杂的描述吗？
  ∃ (n : Nat),
  ∃ (m : Nat → GameState),
    (g = m n)
    ∧
    (is_win (m 0))
    ∧
    (∀ (i : Nat), i < n → allowed_move (m i) (m (i + 1)))

theorem done {n : Nat} : can_win ⟨n,n⟩ := sorry

theorem step_left {p g : Nat} (h : can_win ⟨p, g⟩) : can_win ⟨p + 1, g⟩ :=
  let n := p + 1
  ⟨n,
   λ i => sorry,
   by admit,
   by admit,
   λ i h => by admit⟩

theorem step_right {p g : Nat} (h : can_win ⟨p + 1, g⟩) : can_win ⟨p, g⟩ := sorry

example : can_win {position := 11, goal := 7} :=
by apply step_left
   apply step_left
   apply step_left
   apply step_left
   exact done

example : can_win {position := 9, goal := 11} :=
by apply step_right
   apply step_right
   exact done
