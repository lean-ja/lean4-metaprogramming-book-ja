/-
--#--
#  Lean4 Cheat-sheet

--#--
# Lean4 チートシート

--#--
##  Extracting information

--#--
## 情報の抽出

--#--
* Extract the goal: `Lean.Elab.Tactic.getMainGoal`

--#--
* ゴールの抽出：`Lean.Elab.Tactic.getMainGoal`

--#--
  Use as `let goal ← Lean.Elab.Tactic.getMainGoal`
* Extract the declaration out of a metavariable: `mvarId.getDecl`
  when `mvarId : Lean.MVarId` is in context.
  For instance, `mvarId` could be the goal extracted using `getMainGoal`
* Extract the type of a metavariable: `mvarId.getType`
  when `mvarId : Lean.MVarId` is in context.
* Extract the type of the main goal: `Lean.Elab.Tactic.getMainTarget`

--#--
  これは `let goal ← Lean.Elab.Tactic.getMainGoal` のように使います。
* メタ変数からの宣言の抽出：`mvarId.getDecl`、ここで `mvarId : Lean.MVarId` がコンテキストにあるとします。例えば、ゴールの `mvarId` は `getMainGoal` を使用して抽出することができます。
* メタ変数の型の抽出：`mvarId.getType`、ここで `mvarId : Lean.MVarId` がコンテキストにあるとします。
* メインのゴールの型の抽出：`Lean.Elab.Tactic.getMainTarget`

--#--
  Use as `let goal_type ← Lean.Elab.Tactic.getMainTarget`

--#--
  これは `let goal_type ← Lean.Elab.Tactic.getMainTarget` のように使います。

--#--
  Achieves the same as
--#--
  これは下記と同じ結果になります。

```lean
let goal ← Lean.Elab.Tactic.getMainGoal
let goal_type ← goal.getType
```
--#--
* Extract local context: `Lean.MonadLCtx.getLCtx`

--#--
* ローカルコンテキストの抽出：`Lean.MonadLCtx.getLCtx`

--#--
  Use as `let lctx ← Lean.MonadLCtx.getLCtx`
* Extract the name of a declaration: `Lean.LocalDecl.userName ldecl`
  when `ldecl : Lean.LocalDecl` is in context
* Extract the type of an expression: `Lean.Meta.inferType expr`
  when `expr : Lean.Expr` is an expression in context

--#--
  これは `let lctx ← Lean.MonadLCtx.getLCtx` のように使います。
* 宣言の名前の抽出：`Lean.LocalDecl.userName ldecl`、ここで `ldecl : Lean.LocalDecl` がコンテキストにあるとします。
* 式の型の抽出：`Lean.Meta.inferType expr`、ここで `expr : Lean.Expr` がコンテキストにあるとします。

--#--
  Use as `let expr_type ← Lean.Meta.inferType expr`

--#--
  これは `let expr_type ← Lean.Meta.inferType expr` のように使います。


--#--
##  Playing around with expressions

--#--
## 式で遊ぶ

--#--
* Convert a declaration into an expression: `Lean.LocalDecl.toExpr`

--#--
* 宣言を式に変換する：`Lean.LocalDecl.toExpr`

--#--
  Use as `ldecl.toExpr`, when `ldecl : Lean.LocalDecl` is in context

--#--
  これは `ldecl : Lean.LocalDecl` がコンテキストにある場合に `ldecl.toExpr` のように使います。

--#--
  For instance, `ldecl` could be `let ldecl ← Lean.MonadLCtx.getLCtx`
* Check whether two expressions are definitionally equal: `Lean.Meta.isDefEq ex1 ex2`
  when `ex1 ex2 : Lean.Expr` are in context. Returns a `Lean.MetaM Bool`
* Close a goal: `Lean.Elab.Tactic.closeMainGoal expr`
  when `expr : Lean.Expr` is in context

--#--
  この `ldecl` は例えば、`let ldecl ← Lean.MonadLCtx.getLCtx` などで取得されます。
* 2つの式が定義上等しいかどうかのチェック：`Lean.Meta.isDefEq ex1 ex2`、ここで `ex1 ex2 : Lean.Expr` がコンテキストにあるとします。これは `Lean.MetaM Bool` を返します。
* ゴールを閉じる：`Lean.Elab.Tactic.closeMainGoal expr`、ここで `expr : Lean.Expr` がコンテキストにあるとします。

--#--
##  Further commands

--#--
## さらなるコマンド

--#--
* meta-sorry: `Lean.Elab.admitGoal goal`, when `goal : Lean.MVarId` is the current goal

--#--
* メタ-sorry：`Lean.Elab.admitGoal goal`、ここで `goal : Lean.MVarId` がコンテキストにあるとします。

--#--
##  Printing and errors

--#--
## 表示とエラー

--#--
* Print a "permanent" message in normal usage:

--#--
* 通常の用途での「永久な」メッセージの表示：

  `Lean.logInfo f!"Hi, I will print\n{Syntax}"`
--#--
* Print a message while debugging:

--#--
* デバッグ中のメッセージの表示：

  `dbg_trace f!"1) goal: {Syntax_that_will_be_interpreted}"`.
--#--
* Throw an error: `Lean.Meta.throwTacticEx name mvar message_data`
  where `name : Lean.Name` is the name of a tactic and `mvar` contains error data.

--#--
* 例外を投げる：`Lean.Meta.throwTacticEx name mvar message_data`、ここで `name : Lean.Name` はタクティクの名前で `mvar` はエラーのデータを保持しているとします。

--#--
  Use as `Lean.Meta.throwTacticEx `tac goal (m!"unable to find matching hypothesis of type ({goal_type})")`
  where the `m!` formatting builds a `MessageData` for better printing of terms

--#--
  これは ``Lean.Meta.throwTacticEx `tac goal (m!"unable to find matching hypothesis of type ({goal_type})")`` のように用い、ここでフォーマッタ `m!` は項をより見やすく表示する `MessageData` を構築します。

TODO: Add?
* Lean.LocalContext.forM
* Lean.LocalContext.findDeclM?
-/
