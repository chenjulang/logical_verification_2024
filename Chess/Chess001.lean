import Lean
import Mathlib.Data.List.Basic
import Mathlib.Tactic.CasesM
import ChessWidget
import Lean.Data.Json.FromToJson

declare_syntax_cat chess_square
declare_syntax_cat horizontal_border
declare_syntax_cat game_top_row
declare_syntax_cat game_bottom_row
declare_syntax_cat game_row

syntax "═" : horizontal_border

syntax "\n╔" horizontal_border* "╗\n" : game_top_row

syntax "╚" horizontal_border* "╝\n" : game_bottom_row

syntax "║" chess_square* "║\n" : game_row

syntax "♙]" : chess_square -- white pawn
syntax "♘]" : chess_square -- white knight
syntax "♗]" : chess_square -- white bishop
syntax "♖]" : chess_square -- white rook
syntax "♕]" : chess_square -- white queen
syntax "♔]" : chess_square -- white king
syntax "♟]" : chess_square -- black pawn
syntax "♞]" : chess_square -- black knight
syntax "♝]" : chess_square -- black bishop
syntax "♜]" : chess_square -- black bishop
syntax "♛]" : chess_square -- black queen
syntax "♚]" : chess_square -- black king

syntax "░░" : chess_square -- light square
syntax "▓▓" : chess_square -- dark square
syntax "♔}" : chess_square -- white king and it's white's move
syntax "♚}" : chess_square -- black king and it's black's move

syntax:max game_top_row game_row* game_bottom_row : term

structure Coords where
  row : Nat
  col : Nat
deriving DecidableEq, Repr, Inhabited

def Coords.range : List Coords := Id.run do
  let mut result := []
  for r in [0:8] do
    for c in [0:8] do
      result := ⟨r,c⟩ :: result
  return result.reverse
-- #eval Coords.range 生成了一个列表，棋盘上所有的坐标

-- 上下左右操作。
def Coords.up (c : Coords) : Option Coords :=
 if c.row > 0
 then some { c with row := c.row - 1 }
 else none

def Coords.down (c : Coords) : Option Coords :=
 if c.row + 1 < 8
 then some { c with row := c.row + 1 }
 else none

def Coords.left (c : Coords) : Option Coords :=
 if c.col > 0
 then some { c with col := c.col - 1 }
 else none

def Coords.right (c : Coords) : Option Coords :=
 if c.col + 1 < 8
 then some { c with col := c.col + 1 }
 else none

-- bind是？复合？
-- 第一个不是none才会有some输出，否则也是none
-- @[inline] protected def bind : Option α → (α → Option β) → Option β
--   | none,   _ => none
--   | some a, b => b a
-- 四个45度方向移动一次。
def Coords.ul (c : Coords) : Option Coords :=
 c.up.bind Coords.left

def Coords.ur (c : Coords) : Option Coords :=
 c.up.bind Coords.right

def Coords.dl (c : Coords) : Option Coords :=
 c.down.bind Coords.left

def Coords.dr (c : Coords) : Option Coords :=
 c.down.bind Coords.right


-- knight's moves
-- 这是错了吗？为什么走了左上，还有走左？原来是骑士，“马”走“日”
def Coords.nm1 (c : Coords) : Option Coords :=
 c.ul.bind Coords.left

def Coords.nm2 (c : Coords) : Option Coords :=
 c.ul.bind Coords.up

def Coords.nm3 (c : Coords) : Option Coords :=
 c.ur.bind Coords.up

def Coords.nm4 (c : Coords) : Option Coords :=
 c.ur.bind Coords.right

def Coords.nm5 (c : Coords) : Option Coords :=
 c.dr.bind Coords.right

def Coords.nm6 (c : Coords) : Option Coords :=
 c.dr.bind Coords.down

def Coords.nm7 (c : Coords) : Option Coords :=
 c.dl.bind Coords.down

def Coords.nm8 (c : Coords) : Option Coords :=
 c.dl.bind Coords.left

inductive Piece where
| pawn : Piece
| knight : Piece
| bishop : Piece
| rook : Piece
| queen : Piece
| king : Piece
deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

inductive Side where
| white : Side
| black : Side
deriving DecidableEq, Repr, Inhabited, Lean.ToJson, Lean.FromJson

def Side.other : Side -> Side
| white => black
| black => white
