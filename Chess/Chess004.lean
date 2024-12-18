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


-- 003new:


macro_rules
| `(╔ $tb:horizontal_border* ╗
    $rows:game_row*
    ╚ $bb:horizontal_border* ╝) =>
      do if rows.size != 8 then Lean.Macro.throwError "chess board must have 8 rows"
         if tb.size != 8 * 2 || bb.size != 8 * 2 then
           Lean.Macro.throwError "chess board must have 8 columns"
         let rows' ← Array.mapM termOfGameRow rows
         let turns := (Array.map turnsOfRow rows).toList.join
         let whiteTurn := turns.contains (.some Side.white)
         let blackTurn := turns.contains (.some Side.black)
         if whiteTurn ∧ blackTurn then
           Lean.Macro.throwError "cannot be both white's turn and black's turn"
         if whiteTurn
         then
           `(Position.mk [$rows',*] .white)
         else
           `(Position.mk [$rows',*] .black)

def syntaxOfSquare (turn : Side) : (Piece × Side) →
  Lean.PrettyPrinter.Delaborator.DelabM (Lean.TSyntax `chess_square)
| (Piece.pawn, Side.white) => `(chess_square| ♙])
| (Piece.knight, Side.white) => `(chess_square| ♘])
| (Piece.bishop, Side.white) => `(chess_square| ♗])
| (Piece.rook, Side.white) => `(chess_square| ♖])
| (Piece.queen, Side.white) => `(chess_square| ♕])
| (Piece.king, Side.white) =>
  match turn with
  | .white => `(chess_square| ♔})
  | .black => `(chess_square| ♔])
| (Piece.pawn, Side.black) => `(chess_square| ♟])
| (Piece.knight, Side.black) => `(chess_square| ♞])
| (Piece.bishop, Side.black) => `(chess_square| ♝])
| (Piece.rook, Side.black) => `(chess_square| ♜])
| (Piece.queen, Side.black) => `(chess_square| ♛])
| (Piece.king, Side.black) =>
  match turn with
  | .white => `(chess_square| ♚])
  | .black => `(chess_square| ♚})

def extractSquare : Lean.Expr → Lean.MetaM (Option (Piece × Side))
| exp => do
    let exp' ← Lean.Meta.whnf exp
    match exp'.getAppFn.constName!.toString with
    | "Option.none" => return none
    | "Option.some" =>
      let v := exp'.getAppArgs[1]!
      --let s := v.getAppFn.constName!.toString
      let args := v.getAppArgs
      match args[2]!.constName!, args[3]!.constName! with
      | `Piece.pawn, `Side.white => return some (Piece.pawn, Side.white)
      | `Piece.knight, `Side.white => return some (Piece.knight, Side.white)
      | `Piece.bishop, `Side.white => return some (Piece.bishop, Side.white)
      | `Piece.rook, `Side.white => return some (Piece.rook, Side.white)
      | `Piece.queen, `Side.white => return some (Piece.queen, Side.white)
      | `Piece.king, `Side.white => return some (Piece.king, Side.white)
      | `Piece.pawn, `Side.black => return some (Piece.pawn, Side.black)
      | `Piece.knight, `Side.black => return some (Piece.knight, Side.black)
      | `Piece.bishop, `Side.black => return some (Piece.bishop, Side.black)
      | `Piece.rook, `Side.black => return some (Piece.rook, Side.black)
      | `Piece.queen, `Side.black => return some (Piece.queen, Side.black)
      | `Piece.king, `Side.black => return some (Piece.king, Side.black)
      | _, _ => pure ()
      return none
    | other =>
      dbg_trace "unexpected const {other}"
      return none

partial def extractRowAux : Lean.Expr → Lean.MetaM (List (Option (Piece × Side)))
| exp => do
  let exp' ← Lean.Meta.whnf exp
  let f := Lean.Expr.getAppFn exp'
  match f.constName!.toString with
  | "List.cons" =>
      let consArgs := Lean.Expr.getAppArgs exp'
      let rest ← extractRowAux consArgs[2]!
      let square ← extractSquare consArgs[1]!
      return square :: rest
  | "List.nil" =>
      return []
  | other =>
       dbg_trace "unrecognized constant: {other}"
       return []

partial def extractRow : Lean.Expr → Lean.MetaM (List (Option (Piece × Side)))
| exp => do
    if exp.getAppFn.constName!.toString ≠ "List.cons" then
      throwError "expected list: {exp.getAppFn.constName!.toString}"
    let l ← extractRowAux exp
    return l

partial def extractRowList : Lean.Expr → Lean.MetaM (List (List (Option (Piece × Side))))
| exp => do
  let exp':Lean.Expr ← (Lean.Meta.whnf exp)
  let f := Lean.Expr.getAppFn exp'
  match f.constName!.toString with
  | "List.cons" =>
       let consArgs := Lean.Expr.getAppArgs exp'
       let rest ← extractRowList consArgs[2]!
       let row ← extractRow consArgs[1]!
       return row :: rest
  | "List.nil" =>
       return []
  | other =>
       throwError "unrecognized constant: {other}"

partial def extractPosition : Lean.Expr → Lean.MetaM Position
| exp => do
    let exp': Lean.Expr ← Lean.Meta.reduce exp
    let positionArgs := Lean.Expr.getAppArgs exp'
    let squaresList := positionArgs[0]!
    let rows ← extractRowList squaresList
    let side ← match positionArgs[1]!.constName! with
                | `Side.white => pure Side.white
                | `Side.black => pure Side.black
                | _ => throwError "unrecognized side"
    return Position.mk rows side

def delabGameRow : Array (Lean.TSyntax `chess_square) →
    Lean.PrettyPrinter.Delaborator.DelabM (Lean.TSyntax `game_row)
| a => `(game_row| ║ $a:chess_square* ║)

def delabPosition : Lean.Expr → Lean.PrettyPrinter.Delaborator.Delab
| e =>
  do guard $ e.getAppNumArgs == 2
     let pos ← extractPosition e
     let topBar := Array.mkArray (8 * 2) $ ← `(horizontal_border| ═)
     let lightSquare ← `(chess_square| ░░)
     let darkSquare ← `(chess_square| ▓▓)

     let mut a : Array (Array (Lean.TSyntax `chess_square)) :=
        Array.ofFn (n := 8) (fun row ↦ Array.ofFn (n := 8)
        (fun col ↦ if (col.val + row.val) % 2 = 0 then darkSquare else lightSquare))

     for coords in Coords.range do
       if let some s := pos.get coords then
         let v ← syntaxOfSquare pos.turn s
         a := a.set! coords.row (a[coords.row]!.set! coords.col v)
       pure ()

     let aa ← Array.mapM delabGameRow a

     `(╔$topBar:horizontal_border*╗
       $aa:game_row*
       ╚$topBar:horizontal_border*╝)

/-- 上面的所有函数都是为这里服务。就是为了让图标先变成对象，然后再在infoview打印出来 -/
@[delab app.Position.mk] def delabPositionMk : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  let e' ← Lean.Meta.reduce e
  delabPosition e'

structure ChessPositionWidgetProps where
  pos? : Option Position := none
  deriving Lean.Server.RpcEncodable

def game_start :=
  ╔════════════════╗
  ║♜]♞]♝]♛]♚]♝]♞]♜]║
  ║♟]♟]♟]♟]♟]♟]♟]♟]║
  ║░░▓▓░░▓▓░░▓▓░░▓▓║
  ║▓▓░░▓▓░░▓▓░░▓▓░░║
  ║░░▓▓░░▓▓░░▓▓░░▓▓║
  ║▓▓░░▓▓░░▓▓░░▓▓░░║
  ║♙]♙]♙]♙]♙]♙]♙]♙]║
  ║♖]♘]♗]♕]♔}♗]♘]♖]║
  ╚════════════════╝

#print game_start -- 图标识别转lean对象，然后再打印成功。


def pos2 :=  ╔════════════════╗
             ║♜]♞]♝]♛]♚}♝]♞]♜]║
             ║♟]♟]♟]♟]♟]♟]♟]♟]║
             ║░░▓▓░░▓▓░░▓▓░░▓▓║
             ║▓▓░░▓▓░░▓▓░░▓▓░░║
             ║░░▓▓░░▓▓♙]▓▓░░▓▓║
             ║▓▓░░▓▓░░▓▓░░▓▓░░║
             ║♙]♙]♙]♙]░░♙]♙]♙]║
             ║♖]♘]♗]♕]♔]♗]♘]♖]║
             ╚════════════════╝

--#print pos2

-----------------------------------
-- end (d)elab, start analysis



-- 004new:
-- 输入坐标的“字符形式”后，能够显示什么东西？

-----------------------------------------------
-- set_option linter.hashCommand false
#widget ChessPositionWidget with { pos? := pos2 : ChessPositionWidgetProps }

def row_to_rank (row : Nat) : Char := Char.ofNat ((8 - row) + (Char.toNat '0'))
def col_to_file (col : Nat) : Char := Char.ofNat (col + (Char.toNat 'a'))

def is_rank (rank : Char) : Bool := '1'.toNat ≤ rank.toNat ∧ rank.toNat ≤ '8'.toNat
def is_file (rank : Char) : Bool := 'a'.toNat ≤ rank.toNat ∧ rank.toNat ≤ 'h'.toNat
def rank_to_row (rank : Char) : Nat := 8 - (rank.toNat - '0'.toNat)
def file_to_col (rank : Char) : Nat := rank.toNat - 'a'.toNat

def is_piece : Char → Bool
| 'K' => true
| 'Q' => true
| 'R' => true
| 'B' => true
| 'N' => true
| _ => false

def char_to_piece : Char → Piece
| 'K' => .king
| 'Q' => .queen
| 'R' => .rook
| 'B' => .bishop
| 'N' => .knight
| _ => .pawn

def piece_to_char : Piece → Option Char
| .king => some 'K'
| .queen => some 'Q'
| .rook => some 'R'
| .bishop => some 'B'
| .knight => some 'N'
| .pawn => none

structure OrdinaryChessMove where
  piece : Piece
  dst : Coords -- destination coords
  capture : Bool
  promote : Option Piece
  disambiguate_col : Option Nat
  disambiguate_row : Option Nat
deriving DecidableEq, Repr

inductive ChessMove where
| CastleShort : ChessMove
| CastleLong : ChessMove
| Ordinary : OrdinaryChessMove → ChessMove
deriving DecidableEq, Repr, Inhabited

instance : ToString ChessMove where
toString : ChessMove → String
| .CastleShort => "O-O"
| .CastleLong => "O-O-O"
| .Ordinary { piece, dst, capture,
              disambiguate_row, disambiguate_col, promote } => Id.run do
  let mut result := []
  if let some p := promote then
    if let some c := piece_to_char p
    then result := '=' :: c :: result

  result := col_to_file dst.col :: row_to_rank dst.row :: result

  if capture then
    result := '×' :: result

  if let some r := disambiguate_row then
    result := row_to_rank r :: result
  if let some c := disambiguate_col then
    result := col_to_file c :: result

  if let some c := piece_to_char piece
  then result := c :: result
  return String.mk result

def ChessMove.ofString : String → Option ChessMove
| "O-O" => some .CastleShort
| "O-O-O" => some .CastleLong
| s => Id.run do
  let mut piece := Piece.pawn
  let mut rest := s.toList
  match rest with
  | [] => return none | [_] => return none
  | p :: cs =>
    if is_piece p
    then
        piece := char_to_piece p
        rest := cs
    else
        piece := .pawn

  -- parsing the rest is easiest in reverse
  let mut rrest := rest.reverse
  let mut promote := none
  match rrest with
  | p :: '=' :: cs =>
    if is_piece p
    then promote := some (char_to_piece p)
         rrest := cs
    else return none
  | _ => pure ()

  let crow :: cfile :: cs := rrest | return none
  if ¬is_file cfile then return none
  if ¬is_rank crow then return none
  let dst := { row := rank_to_row crow, col := file_to_col cfile}
  rrest := cs

  let mut capture := false
  match rrest with
  | '×' :: cs =>
        capture := true
        rrest := cs
  | _ => pure ()

  let mut disambiguate_row : Option Nat := none
  let mut disambiguate_col : Option Nat := none
  match rrest with
  | c :: cs =>
    if is_file c
    then disambiguate_col := some (file_to_col c)
         if ¬cs.isEmpty then return none
    else
      if is_rank c
      then disambiguate_row := some (rank_to_row c)
           match cs with
           | [] => pure ()
           | [c] =>
             if is_file c
             then disambiguate_col := some (file_to_col c)
             else return none
           | _ => return none
    rrest := cs
  | [] => pure ()

  return some (.Ordinary {piece, dst, capture,
                          disambiguate_row, disambiguate_col, promote})

#eval (ChessMove.ofString "Qa6×d3").map ToString.toString
#eval (ChessMove.ofString "e×f5")
