// Lean compiler output
// Module: ChessWidget
// Imports: Init Lean
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static uint64_t l_ChessPositionWidget___closed__2;
uint64_t lean_string_hash(lean_object*);
static lean_object* l_ChessPositionWidget___closed__3;
static lean_object* l_ChessPositionWidget___closed__1;
LEAN_EXPORT lean_object* l_ChessPositionWidget;
LEAN_EXPORT lean_object* l_ChessPositionWidget___closed__3___boxed__const__1;
static lean_object* _init_l_ChessPositionWidget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nimport * as React from 'react';\n// Mapping of piece names to symbols\nconst pieceSymbols = {\n  'pawn': '♟',\n  'rook': '♜',\n  'knight': '♞',\n  'bishop': '♝',\n  'queen': '♛',\n  'king': '♚'\n};\n\n// Helper function to determine the square color\nfunction getSquareColor(row, col) {\n  return (row + col) % 2 === 0 \? '#b58863' : '#f0d9b5';\n}\n\n// Chessboard component with inline styles\nexport default function ChessPositionWidget(props) {\n  const emptyBoard = Array(8).fill(Array(8).fill(null));\n\n  const { turn = 'nobody', squares = emptyBoard } = props.pos || {};\n\n  const chessBoardStyle = {\n    display: 'flex',\n    flexDirection: 'column',\n  };\n\n  const chessRowStyle = {\n    display: 'flex',\n  };\n\n  const chessSquareStyle = {\n    width: '40px',\n    height: '40px',\n    display: 'flex',\n    alignItems: 'center',\n    justifyContent: 'center',\n  };\n\n  const chessPieceStyle = (color) => ({\n    fontSize: '40px',\n    color: color === 'white' \? '#fff' : '#000',\n  });\n\n  const rows = squares.map((row, rowIndex) => {\n    const columns = row.map((square, colIndex) => {\n      const squareColor = getSquareColor(rowIndex, colIndex);\n      const piece = square \? pieceSymbols[square[0]] : null;\n      const pieceColor = square \? square[1] : null;\n\n      return React.createElement(\n        'div',\n        {\n          key: `${rowIndex}-${colIndex}`,\n          style: { ...chessSquareStyle, backgroundColor: squareColor },\n        },\n        React.createElement(\n          'span',\n          { style: chessPieceStyle(pieceColor) },\n          piece\n        )\n      );\n    });\n\n    return React.createElement(\n      'div',\n      { key: `row-${rowIndex}`, style: chessRowStyle },\n      columns\n    );\n  });\n\n  return React.createElement(\n    'div',\n    {},\n    React.createElement('h3', {}, `Turn: ${turn}`),\n    React.createElement('div', { style: chessBoardStyle }, rows)\n  );\n}\n", 1879);
return x_1;
}
}
static uint64_t _init_l_ChessPositionWidget___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_ChessPositionWidget___closed__1;
x_2 = lean_string_hash(x_1);
return x_2;
}
}
static lean_object* _init_l_ChessPositionWidget___closed__3___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_ChessPositionWidget___closed__2;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_ChessPositionWidget___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ChessPositionWidget___closed__1;
x_2 = l_ChessPositionWidget___closed__3___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_ChessPositionWidget() {
_start:
{
lean_object* x_1; 
x_1 = l_ChessPositionWidget___closed__3;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ChessWidget(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ChessPositionWidget___closed__1 = _init_l_ChessPositionWidget___closed__1();
lean_mark_persistent(l_ChessPositionWidget___closed__1);
l_ChessPositionWidget___closed__2 = _init_l_ChessPositionWidget___closed__2();
l_ChessPositionWidget___closed__3___boxed__const__1 = _init_l_ChessPositionWidget___closed__3___boxed__const__1();
lean_mark_persistent(l_ChessPositionWidget___closed__3___boxed__const__1);
l_ChessPositionWidget___closed__3 = _init_l_ChessPositionWidget___closed__3();
lean_mark_persistent(l_ChessPositionWidget___closed__3);
l_ChessPositionWidget = _init_l_ChessPositionWidget();
lean_mark_persistent(l_ChessPositionWidget);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
