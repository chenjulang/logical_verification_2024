lean4-maze 精益迷宫
This repo shows how maze solving can be encoded as theorem proving using the Lean 4 programming language.
该存储库展示了如何使用 Lean 4 编程语言将迷宫求解编码为定理证明。

It draws inspration from https://github.com/kbuzzard/maze-game.
它从 https://github.com/kbuzzard/maze-game 中汲取灵感。

How To Play 怎么玩
First, install Lean 4 on your computer: https://leanprover.github.io/lean4/doc/setup.html
首先，在计算机上安装 Lean 4：https://leanprover.github.io/lean4/doc/setup.html

Then open Maze.lean in emacs or VSCode.
然后在 emacs 或 VSCode 中打开 Maze.lean 。

You can define a maze like this:
你可以像这样定义一个迷宫：

def maze := ╔════════╗
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
The @ symbol denotes your current location. You are free to move within light-colored cells. The dark-colored cells are walls.
@ 符号表示您当前的位置。您可以在浅色牢房内自由移动。深色细胞是墙壁。

Your goal is to escape the maze at any of its borders.
你的目标是逃离迷宫的任何边界。

You can interactively solve a maze like this:
您可以像这样交互式地解决迷宫：

example : can_escape maze :=
 by south
    east
    south
    south
As you make progress, Lean's goal view will desplay your current state. For example, after the moves made above, the state is shown as:
当您取得进步时，Lean 的目标视图将显示您当前的状态。例如，进行上述动作后，状态显示为：

⊢ can_escape
    (
        ╔════════╗
        ║▓▓▓▓▓▓▓▓║
        ║▓░▓░▓░▓▓║
        ║▓░▓░░░▓▓║
        ║▓░░▓░▓▓▓║
        ║▓▓░▓@▓░░║
        ║▓░░░░▓░▓║
        ║▓░▓▓▓▓░▓║
        ║▓░░░░░░▓║
        ║▓▓▓▓▓▓▓▓║
        ╚════════╝
        )
The main moves available to you at any point are north, south, east, and west.
您随时可以使用的主要动作是 north 、 south 、 east 和 west 。

When you reach the boundary, you can finish your proof with one of apply escape_north, apply escape_south, apply escape_east, or apply escape_west.
当到达边界时，您可以使用 apply escape_north 、 apply escape_south 、 apply escape_east 或 apply escape_west 之一完成证明。

how does it work? 它是如何运作的？
The mazes as drawn above are actual valid Lean 4 syntax!
上面绘制的迷宫是真正有效的 Lean 4 语法！

We define new syntax categories and some macro_rules for elaborating them into valid values.
我们定义了新的语法类别和一些 macro_rules 来将它们细化为有效值。

To get Lean to render the values back in the above format, we define a delaboration function and register it with the pretty printer.
为了让 Lean 以上述格式渲染值，我们定义了一个详细函数并将其注册到漂亮的打印机上。

Lean 4 lets us do all of this in-line, in ordinary Lean 4 code.
Lean 4 让我们可以在普通的 Lean 4 代码中内联完成所有这些工作。