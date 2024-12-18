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



-- 002new:

-- We store the board as a List of Lists.
-- You might think that Array would be more efficient than List.
-- However, as far as kernel evaluation is concerned, Array is
-- just a wrapper of List, and additionally requires well-founded
-- recursion in some situations:
-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60decide.60.20fails.20after.20leanprover.2Flean4.3Anightly-2024-05-11/near/449757859

-- row, column.
-- (0,0) is the upper left corner (a8)
abbrev Squares := List (List (Option (Piece × Side)))

/-- 表示某个象棋的实时局势 -/
structure Position where
  squares : Squares
  turn : Side
deriving DecidableEq, Repr, Inhabited,  Lean.ToJson, Lean.FromJson

def Position.get (p : Position) (c : Coords) : Option (Piece × Side) :=
  (p.squares.get! c.row).get! c.col

def Position.sideAt (p : Position) (c : Coords) : Option Side :=
  match p.get c with
  | some (_, s) => some s
  | none => none

def Position.set (p : Position) (c : Coords) (s : Option (Piece × Side)) : Position :=
  { p with squares := p.squares.set c.row ((p.squares.get! c.row).set c.col s) }

-- 看看下面这些定义的函数的效果都是怎样的：

def termOfSquare : Lean.TSyntax `chess_square → Lean.MacroM (Lean.TSyntax `term)
| `(chess_square| ░░) => `(none)
| `(chess_square| ▓▓) => `(none)
| `(chess_square| ♙]) => `(some (Piece.pawn, Side.white))
| `(chess_square| ♘]) => `(some (Piece.knight, Side.white))
| `(chess_square| ♗]) => `(some (Piece.bishop, Side.white))
| `(chess_square| ♖]) => `(some (Piece.rook, Side.white))
| `(chess_square| ♕]) => `(some (Piece.queen, Side.white))
| `(chess_square| ♔]) => `(some (Piece.king, Side.white))
| `(chess_square| ♔}) => `(some (Piece.king, Side.white))
| `(chess_square| ♟]) => `(some (Piece.pawn, Side.black))
| `(chess_square| ♞]) => `(some (Piece.knight, Side.black))
| `(chess_square| ♝]) => `(some (Piece.bishop, Side.black))
| `(chess_square| ♜]) => `(some (Piece.rook, Side.black))
| `(chess_square| ♛]) => `(some (Piece.queen, Side.black))
| `(chess_square| ♚]) => `(some (Piece.king, Side.black))
| `(chess_square| ♚}) => `(some (Piece.king, Side.black))
| _ => Lean.Macro.throwError "unknown chess square"


def termOfGameRow : Lean.TSyntax `game_row → Lean.MacroM (Lean.TSyntax `term)
| `(game_row| ║$squares:chess_square*║) =>
      do if squares.size != 8
         then Lean.Macro.throwError "row has wrong size"
         let squares' ← Array.mapM termOfSquare squares
         `([$squares',*])
| _ => Lean.Macro.throwError "unknown game row"

def turnOfSquare : Lean.TSyntax `chess_square → Option Side
| `(chess_square| ♔}) => some (Side.white)
| `(chess_square| ♚}) => some (Side.black)
| _ => none

def turnsOfRow : Lean.TSyntax `game_row → List (Option Side)
| `(game_row| ║$squares:chess_square*║) =>
      squares.toList.map turnOfSquare
| _ => []
