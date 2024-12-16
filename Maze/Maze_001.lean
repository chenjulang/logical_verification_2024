import Lean

/-- 001new：游戏状态 -/
structure GameState where
  position : Nat
  goal : Nat

-- 001new：游戏里的格子放的什么 [start
inductive CellContents where
  | empty  : CellContents
  | player : CellContents
  | goal   : CellContents

/-- 通过游戏里的所有格子放的什么，推断出玩家player在哪，出口goal在哪 -/
def game_state_from_cells :
List CellContents → GameState
 | [] =>
  ⟨0,0⟩
 | CellContents.empty :: cells => -- cells是自定义的名字
  let ⟨p,g⟩ := game_state_from_cells cells
  -- dbg_trace "1";
  ⟨p+1, g+1⟩
 | CellContents.player::cells =>
  let ⟨p,g⟩ := game_state_from_cells cells
  -- dbg_trace "2";
  ⟨0, g+1⟩
 | CellContents.goal::cells =>
  let ⟨p,g⟩ := game_state_from_cells cells
  -- dbg_trace "3";
  ⟨p+1, 0⟩

-- 举例：
#reduce game_state_from_cells
  [CellContents.goal, CellContents.player, CellContents.empty, CellContents.empty]
-- { position := 1, goal := 0 }
#reduce game_state_from_cells
  [CellContents.goal, CellContents.empty, CellContents.player, CellContents.empty]
-- { position := 2, goal := 0 }
#reduce game_state_from_cells
  [CellContents.player, CellContents.goal, ]
#reduce game_state_from_cells -- 如果后面没出现goal和player的话，有bug：
  [ CellContents.empty, CellContents.empty, CellContents.empty, CellContents.empty,]


-- 游戏里的格子放的什么 end]


-- 001new：syntax语法 [start

-- “句法”的类型，无意义的先定义，后面再说具体哪些是这种类型的
declare_syntax_cat game_cell
declare_syntax_cat game_cell_sequence

syntax "★" : game_cell
syntax "░" : game_cell
syntax "@" : game_cell

syntax game_cell* : game_cell_sequence -- “句法”

syntax "┤" game_cell_sequence "├ ": term
--这里可以看出， “句法” 能正则匹配；而且能显式的说，这就是一个term，可以直接当做“人写的代码”解释。
syntax "┤{" game_cell_sequence "}├": term


macro_rules
| `(┤├) => `( (⟨1, 3⟩ : GameState) )
-- 这里可以看出，机器直接看到代码长这样，就直接解释成某个特定的东西。
| `(┤$cell:game_cell $cells:game_cell*├) => `( (⟨123, 999⟩ : GameState) )
-- 这里可以看出，机器看代码时，还学会了正则匹配，而且自动赋予变量名。正常操作。虽然解释成的东西没用这些变量，应该后面迭代会有。

--| `(┤░░├) => `((⟨1, 3⟩ : GameState))

-- #check ┤░░░░├ -- 打印： { position := 123, goal := 999 } : GameState

-- #check ┤░░
--         ░░├ -- 打印： { position := 123, goal := 999 } : GameState

-- syntax语法 end]

-- 两个状态是可以互相走到的
def allowed_move : GameState → GameState → Prop
| ⟨p1, g1⟩, ⟨p2, g2⟩ =>
-- 意思是，玩家在一维迷宫里，往前或往后走一步，是允许的。
    (p2 + 1 = p1 ∧ g1 = g2)
    ∨
    (p2 = p1 + 1 ∧ g1 = g2)

def is_win : GameState → Prop
-- 玩家走到了出口goal
| ⟨n, m⟩ => n = m

def can_win (g : GameState) : Prop := -- 这么复杂的描述吗？
  ∃ (n : Nat),
  ∃ (m : Nat → GameState),
    (g = m n) -- 玩家在列表m中，的索引n位置。
    ∧
    (is_win (m 0)) -- 出口在列表m中，的索引0位置
    ∧
    (∀ (i : Nat), i < n → allowed_move (m i) (m (i + 1))) -- 玩家去出口的路上相邻的任意2个位置都是可以互通的。

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
