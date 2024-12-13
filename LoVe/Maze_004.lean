import Lean
set_option linter.unusedVariables false
-- import Lean.PrettyPrinter.Delaborator.SubExpr

-- open Lean.SubExpr



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

-- #reduce ┤░@░★░░├

-- #check GameState.mk

-- 002new：
-- @[appUnexpander GameState]
-- def unexpandGameState : Lean.PrettyPrinter.Unexpander
--  | `({ position := $p, goal := $g}) => `(┤░@░★░░├)
  -- | `(GameState $p $g) => `(┤░@░░░░★░░├)
  -- | _              => throw ()

-- 003new:
@[delab app.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  -- 004new: delabGameState这个终于正常运行了
  guard $ e.getAppNumArgs == 3
  let p ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.delab
  let g ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppFn
           $ Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.delab
  let s ← Lean.PrettyPrinter.Delaborator.SubExpr.withAppArg Lean.PrettyPrinter.Delaborator.delab
  let e ← `(game_cell| ░)
  let player ← `(game_cell| @)
  let goalc ← `(game_cell| ★)
  let position : Nat := p.raw.isNatLit?.get!
  let goal : Nat := g.raw.isNatLit?.get!
  let size : Nat := s.raw.isNatLit?.get!
  let a0 := Array.mkArray size e
  let a1 := Array.set! a0 position player
  let a2 := Array.set! a1 goal goalc
  dbg_trace position
  dbg_trace p
  dbg_trace g
  dbg_trace s
  `(┤$a2:game_cell*├)

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
by apply step_right
   apply step_right
   exact done
