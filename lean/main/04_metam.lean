/-
# `MetaM`

--#--
The Lean 4 metaprogramming API is organised around a small zoo of monads. The
four main ones are:

--#--
Lean4のメタプログラミングAPIはモナドの小さな動物園を中心に構成されています。主なものは4つあります：

--#--
- `CoreM` gives access to the *environment*, i.e. the set of things that
  have been declared or imported at the current point in the program.
- `MetaM` gives access to the *metavariable context*, i.e. the set of
  metavariables that are currently declared and the values assigned to them (if
  any).
- `TermElabM` gives access to various information used during elaboration.
- `TacticM` gives access to the list of current goals.

--#--
- `CoreM` は **環境** （environment）へのアクセスを提供します。環境とは、そのプログラムでその時点までに宣言やインポートされたもののあつまりです。
- `MetaM` は **メタ変数コンテキスト** へのアクセスを提供します。これはその時点までに宣言されているメタ変数と（もしあれば）それらに割り当てられている値のあつまりです。
- `TermElabM` はエラボレーションの際に使用される様々な情報へのアクセスを提供します。
- `TacticM` は現在のゴールのリストにアクセスできます。

--#--
These monads extend each other, so a `MetaM` operation also has access to the
environment and a `TermElabM` computation can use metavariables. There are also
other monads which do not neatly fit into this hierarchy, e.g. `CommandElabM`
extends `MetaM` but neither extends nor is extended by `TermElabM`.

--#--
これらのモナドはお互いに拡張されているため、`MetaM` の操作は環境へのアクセスも持ち、`TermElabM` の計算ではメタ変数を使うことができます。また、この階層にうまく当てはまらないモナドもあります。例えば `CommandMonadM` は `MetaM` を拡張していますが、`TermElabM` を拡張することも、されることもありません。

--#--
This chapter demonstrates a number of useful operations in the `MetaM` monad.
`MetaM` is of particular importance because it allows us to give meaning to
every expression: the environment (from `CoreM`) gives meaning to constants like
`Nat.zero` or `List.map` and the metavariable context gives meaning to both
metavariables and local hypotheses.
--#--
この章では `MetaM` モナドの便利な操作をいくつか紹介します。`MetaM` はすべての式の意味を利用者に与えてくれる点において特に重要です：（`CoreM` からの）環境は `Nat.zero` や `List.map` のような定数に意味を与え、メタ変数コンテキストはメタ変数とローカルの仮定の両方に意味を与えます。
-/

import Lean

open Lean Lean.Expr Lean.Meta

/-!
--#--
## Metavariables

--#--
## メタ変数

--#--
### Overview

--#--
### 概要

--#--
The 'Meta' in `MetaM` refers to metavariables, so we should talk about these
first. Lean users do not usually interact much with metavariables -- at least
not consciously -- but they are used all over the place in metaprograms. There
are two ways to view them: as holes in an expression or as goals.

--#--
`MetaM` の「Meta」はメタ変数のことであるため、まずはメタ変数について話しましょう。Leanのユーザは通常メタ変数とあまり関わりません（少なくとも意識的には）が、これはメタプログラミングではあちこちで使われています。メタ変数には2つの見方があります：式の穴として見るか、ゴールとして見るかです。

--#--
Take the goal perspective first. When we prove things in Lean, we always operate
on goals, such as

--#--
まずはゴールとしての観点について取り上げましょう。Leanで物事を証明するとき、常に次のようなゴールに基づいて操作を行います：

```lean
n m : Nat
⊢ n + m = m + n
```

--#--
These goals are internally represented by metavariables. Accordingly, each
metavariable has a *local context* containing hypotheses (here `[n : Nat, m :
Nat]`) and a *target type* (here `n + m = m + n`). Metavariables also have a
unique name, say `m`, and we usually render them as `?m`.

--#--
これらのゴールは内部的にはメタ変数で表現されます。したがって、各メタ変数は仮定を含む **ローカルコンテキスト** （ここでは `[n : Nat, m : Nat]`）と **ターゲットの型** （ここでは `n + m = m + n`）を持ちます。また、メタ変数は一意な名前、例えば `m` を持ち、通常は `?m` と表記します。

--#--
To close a goal, we must give an expression `e` of the target type. The
expression may contain fvars from the metavariable's local context, but no
others. Internally, closing a goal in this way corresponds to *assigning* the
metavariable; we write `?m := e` for this assignment.

--#--
ゴールを閉じるには、ターゲットの型の式 `e` を与えなければなりません。この式にはメタ変数のローカルコンテキストの fvar を含めることができますが、それ以外を含めることはできません。内部的にはこの方法でゴールを閉じることは、メタ変数を **割当** することに相当します；この割当は `?m := e` と書かれます。

--#--
The second, complementary view of metavariables is that they represent holes
in an expression. For instance, an application of `Eq.trans` may generate two
goals which look like this:

--#--
メタ変数の2つ目の補助的な見方は、メタ変数が式の穴を表すというものでした。例えば、`Eq.trans` を適用すると、次のようなゴールが生成されます：

```lean
n m : Nat
⊢ n = ?x

n m : Nat
⊢ ?x = m
```

--#--
Here `?x` is another metavariable -- a hole in the target types of both goals,
to be filled in later during the proof. The type of `?x` is `Nat` and its local
context is `[n : Nat, m : Nat]`. Now, if we solve the first goal by reflexivity,
then `?x` must be `n`, so we assign `?x := n`. Crucially, this also affects the
second goal: it is "updated" (not really, as we will see) to have target `n =
m`. The metavariable `?x` represents the same expression everywhere it occurs.

--#--
ここで `?x` は別のメタ変数で、両方のゴールのターゲットの型の穴であり、この証明でこの後埋める必要があります。`?x` の型は `Nat` であり、そのローカルコンテキストは `[n : Nat, m : Nat]` です。ここで、最初のゴールを反射律によって解く場合、`?x` は `n` でなければならないため、`?x := n` を割当します。きわめて重要なことですが、これは2番目のゴールにも影響します：2番目のゴールはターゲット `n = m` を持つように「更新」されます（後述しますが、実際には更新はされません）。メタ変数 `?x` は出現するすべての個所で同じ式を表しているのです。

--#--

### Tactic Communication via Metavariables

--#--
### メタ変数を通じたタクティクとの会話

--#--
Tactics use metavariables to communicate the current goals. To see how, consider
this simple (and slightly artificial) proof:
--#--
タクティクはメタ変数を使って現在のゴールを伝えます。その方法を知るために、次の簡単な（そして少々人為的な）証明を考えてみましょう：
-/

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  apply h
  apply h

/-!
--#--
After we enter tactic mode, our ultimate goal is to generate an expression of
type `f (f a) = a` which may involve the hypotheses `α`, `a`, `f` and `h`. So
Lean generates a metavariable `?m1` with target `f (f a) = a` and a local
context containing these hypotheses. This metavariable is passed to the first
`apply` tactic as the current goal.

--#--
タクティクモードに入ると、最終的なゴールは仮定 `α`・`a`・`f`・`h` を含む `f (f a) = a` 型の式を生成することとなります。そこでLeanはターゲット `f (f a) = a` とこれらの仮定を含むローカルコンテキストを持つメタ変数 `?m1` を生成します。このメタ変数は現在のゴールとして最初の `apply` タクティクに渡されます。

--#--
The `apply` tactic then tries to apply `Eq.trans` and succeeds, generating three
new metavariables:

--#--
次に `apply` タクティクで `Ex.trans` を適用を試し成功すると、3つの新しいメタ変数が生成されます：

```lean
...
⊢ f (f a) = ?b

...
⊢ ?b = a

...
⊢ α
```

--#--
Call these metavariables `?m2`, `?m3` and `?b`. The last one, `?b`, stands for
the intermediate element of the transitivity proof and occurs in `?m2` and
`?m3`. The local contexts of all metavariables in this proof are the same, so
we omit them.

--#--
これらのメタ変数は `?m2`・`?m3`・`?b` と呼びます。最後の `?b` は推移律の証明における中間要素を表し、`?m2` と `?m3` に現れます。この証明におけるすべてのメタ変数のローカルコンテキストは同じであるため証明しています。

--#--
Having created these metavariables, `apply` assigns

--#--
これらのメタ変数を作成した後、`apply` は以下を割当し、

```lean
?m1 := @Eq.trans α (f (f a)) ?b a ?m2 ?m3
```

--#--
and reports that `?m2`, `?m3` and `?b` are now the current goals.

--#--
`?m2`・`?m3`・`?b` が現在のゴールとなったことを報告します。

--#--
At this point the second `apply` tactic takes over. It receives `?m2` as the
current goal and applies `h` to it. This succeeds and the tactic assigns `?m2 :=
h (f a)`. This assignment implies that `?b` must be `f a`, so the tactic also
assigns `?b := f a`. Assigned metavariables are not considered open goals, so
the only goal that remains is `?m3`.

--#--
この時点で2番目の `apply` タクティクが処理を引き継ぎます。これは `?m2` を現在のゴールとして受け取り、それを `h` に適用します。これは成功し、タクティクは `?m2 := h (f a)` を割当します。この割当は `?b` が `f a` でなければならないことを意味するため、タクティクは `?b := f a` も割当します。割り当てられたメタ変数はオープンなゴールとはみなされないため、残るゴールは `?m3` だけとなります。

--#--
Now the third `apply` comes in. Since `?b` has been assigned, the target of
`?m3` is now `f a = a`. Again, the application of `h` succeeds and the
tactic assigns `?m3 := h a`.

--#--
ここで3つ目の `apply` がやってきます。`?b` が割り当てられたため、`?m3` のターゲットは `f a = a` となります。ここでも `h` の適用が成功し、タクティクは `?m3 := h a` を割当します。

--#--
At this point, all metavariables are assigned as follows:

--#--
この時点で、すべてのメタ変数が次のように割り当てられました：

```lean
?m1 := @Eq.trans α (f (f a)) ?b a ?m2 ?m3
?m2 := h (f a)
?m3 := h a
?b  := f a
```

--#--
Exiting the `by` block, Lean constructs the final proof term by taking the
assignment of `?m1` and replacing each metavariable with its assignment. This
yields

--#--
`by` ブロックを抜けると、Leanは `?m1` の割当を取り、各メタ変数でその割当を置き換えることで最終的な証明項を構築します。これにより以下を得ます。

```lean
@Eq.trans α (f (f a)) (f a) a (h (f a)) (h a)
```

--#--
The example also shows how the two views of metavariables -- as holes in an
expression or as goals -- are related: the goals we get are holes in the final
proof term.

--#--
この例ではメタ変数の2つの見方（式の穴として、あるいはゴールとして）がどのように関連しているかも示しています：最終的に得られたゴールは、最終的な証明項の穴です。

--#--

### Basic Operations

--#--
### 基本操作

--#--
Let us make these concepts concrete. When we operate in the `MetaM` monad, we
have read-write access to a `MetavarContext` structure containing information
about the currently declared metavariables. Each metavariable is identified by
an `MVarId` (a unique `Name`). To create a new metavariable, we use
`Lean.Meta.mkFreshExprMVar` with type

--#--
これらの概念を具体的にしましょう。`MetaM` モナドで操作を行うとき、現在宣言されているメタ変数に関する情報を含む `MetavarContext` 構造体への読み書きアクセスを持ちます。各メタ変数は `MVarId` （これは一意な `Name` です）で識別されます。新しいメタ変数を作成するには、以下の型の `Lean.Meta.mkFreshExprMVar` を使用します。

```lean
mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural)
    (userName := Name.anonymous) : MetaM Expr
```

--#--
Its arguments are:

--#--
この引数はそれぞれ以下です：

--#--
- `type?`: the target type of the new metavariable. If `none`, the target type
  is `Sort ?u`, where `?u` is a universe level metavariable. (This is a special
  class of metavariables for universe levels, distinct from the expression
  metavariables which we have been calling simply "metavariables".)
- `kind`: the metavariable kind. See the [Metavariable Kinds
  section](#metavariable-kinds) (but the default is usually correct).
- `userName`: the new metavariable's user-facing name. This is what gets printed
  when the metavariable appears in a goal. Unlike the `MVarId`, this name does
  not need to be unique.

--#--
- `type?`：新しいメタ変数のターゲットの型。`none` の場合、ターゲットの型は `Sort ?u` となります。ここで `?u` は宇宙レベルのメタ変数です。（これは宇宙レベルのメタ変数の特別なクラスであり、これまで単に「メタ変数」と呼んできた式についてのメタ変数とは区別されます。）
- `kind`：メタ変数の種（kind）。詳しくは [メタ変数の種](#metavariable-kinds) を参照してください（通常はデフォルト値が正しいです）。
- `userName`：新しいメタ変数のユーザが目にする名前。これはメタ変数がゴールに現れる際に表示されるものになります。`MVarId` と異なり、この名前は一意である必要はありません。

--#--
The returned `Expr` is always a metavariable. We can use `Lean.Expr.mvarId!` to
extract the `MVarId`, which is guaranteed to be unique. (Arguably
`mkFreshExprMVar` should just return the `MVarId`.)

--#--
返却される `Expr` は必ずメタ変数です。一意であることが保証されている `MVarId` を取り出すには `Lean.Expr.mvarId!` を使用します。（ただ、おそらく `mkFreshExprMVar` は `MVarId` を返すはずです）

--#--
The local context of the new metavariable is inherited from the current local
context, more about which in the next section. If you want to give a different
local context, use `Lean.Meta.mkFreshExprMVarAt`.

--#--
新しいメタ変数のローカルコンテキストは現在のローカルコンテキストを継承します。異なるローカルコンテキストを与えたい場合は、`Lean.Meta.mkFreshExprMVarAt` を使用します。

--#--
Metavariables are initially unassigned. To assign them, use
`Lean.MVarId.assign` with type

--#--
メタ変数は初期化時は何も割り当てられません。割当するには以下の型を持つ `Lean.MVarId.assign` を使用します。

```lean
assign (mvarId : MVarId) (val : Expr) : MetaM Unit
```

--#--
This updates the `MetavarContext` with the assignment `?mvarId := val`. You must
make sure that `mvarId` is not assigned yet (or that the old assignment is
definitionally equal to the new assignment). You must also make sure that the
assigned value, `val`, has the right type. This means (a) that `val` must have
the target type of `mvarId` and (b) that `val` must only contain fvars from the
local context of `mvarId`.

--#--
この関数は `MetavarContext` を割当 `?mvarId := val` で更新します。ここでこの `mvarId` が割り当てられていないことを確認しなければなりません（もしくは古い割当と新しい割当が定義上等しいことを確認する必要があります）。また、割り当てられた値 `val` が正しい型であることも確認しなければいけません。これは、(a) `val` が `mvarId` のターゲットの型を持たなければならないこと、(b) `val` が `mvarId` のローカルコンテキストの fvar しか含まなければならないことを意味します。

--#--
If you `#check Lean.MVarId.assign`, you will see that its real type is more
general than the one we showed above: it works in any monad that has access to a
`MetavarContext`. But `MetaM` is by far the most important such monad, so in
this chapter, we specialise the types of `assign` and similar functions.

--#--
`#check Lean.MVarId.assign` を実行すると、その実際の型は上で示したものより一般的であることがわかります：これは `MetavarContext` へアクセスを持つ任意のモナドで機能します。しかし、`MetaM` はその中でも圧倒的に重要であるため、この章では `assign` や類似の関数の型を `MetaM` に限定します。

--#--
To get information about a declared metavariable, use `Lean.MVarId.getDecl`.
Given an `MVarId`, this returns a `MetavarDecl` structure. (If no metavariable
with the given `MVarId` is declared, the function throws an exception.) The
`MetavarDecl` contains information about the metavariable, e.g. its type, local
context and user-facing name. This function has some convenient variants, such
as `Lean.MVarId.getType`.

--#--
宣言されたメタ変数に関する情報を得るには、`Lean.MVarId.getDecl` を使用します。この関数は `MVarId` を渡すと `MetavarDecl` 構造体を返します。（もし指定された `MVarId` を持つメタ変数が宣言されていない場合、この関数は例外を投げます。）この `MetavarDecl` 構造体にはメタ変数についての情報、すなわちメタ変数の型・ローカルコンテキスト・ユーザが目にする名前などが格納されます。この関数には `Lean.MVarId.getType` などの便利なバージョンがあります。

--#--
To get the current assignment of a metavariable (if any), use
`Lean.getExprMVarAssignment?`. To check whether a metavariable is assigned, use
`Lean.MVarId.isAssigned`. However, these functions are relatively rarely
used in tactic code because we usually prefer a more powerful operation:
`Lean.Meta.instantiateMVars` with type

--#--
メタ変数の現在の割り当てを取得するには（もしあれば）、`Lean.getExprMVarAssignment?` を使用します。メタ変数が割り当てられているかどうかを確認するには `Lean.MVarId.isAssigned` を使います。しかし、これらの関数がタクティクのコードで使われることは比較的少ないです。というのも大抵は以下の型を持つより強力な操作 `Lean.Meta.instantiateMVars` が好まれるからです。

```lean
instantiateMVars : Expr → MetaM Expr
```

--#--
Given an expression `e`, `instantiateMVars` replaces any assigned metavariable
`?m` in `e` with its assigned value. Unassigned metavariables remain as they
are.

--#--
式 `e` が与えられている時、`instantiateMVars` は `e` 内で割り当てられているメタ変数 `?m` をその割当値で置き換えます。割り当てられていないメタ変数はそのままになります。

--#--
This operation should be used liberally. When we assign a metavariable, existing
expressions containing this metavariable are not immediately updated. This is a
problem when, for example, we match on an expression to check whether it is an
equation. Without `instantiateMVars`, we might miss the fact that the expression
`?m`, where `?m` happens to be assigned to `0 = n`, represents an equation. In
other words, `instantiateMVars` brings our expressions up to date with the
current metavariable state.

--#--
この操作は自由に使うべきです。メタ変数を割当すると、そのメタ変数を含む既存の式はすぐには更新されません。これは、例えばある式が等式であるかどうかをチェックするためにマッチを行う際に問題になります。`instantiateMVars` を使わない場合、式 `?m` が、例えばたまたま `0 = n` が割り当てられているとした時に、それが等式を表していることを見逃してしまうかもしれません。言い換えると、`instantiateMVars` は式を現在のメタ変数の状態に合わせてくれるのです。

--#--
Instantiating metavariables requires a full traversal of the input expression,
so it can be somewhat expensive. But if the input expression does not contain
any metavariables, `instantiateMVars` is essentially free. Since this is the
common case, liberal use of `instantiateMVars` is fine in most situations.

--#--
メタ変数のインスタンス化するには、入力式を完全に走査する必要があるため、実行コストが多少高くつくことがあります。しかし、入力式にメタ変数が含まれていない場合、`instantiateMVars` は基本的にタダです。これが一般的なケースであるため、ほとんどの状況では `instantiateMVars` の自由な使用は問題ありません。

--#--
Before we go on, here is a synthetic example demonstrating how the basic
metavariable operations are used. More natural examples appear in the following
sections.
--#--
先に進む前に、基本的なメタ変数操作がどのように使われるかを示す総合的な例を挙げましょう。より自然な例は以下の節に挙げます。
-/

#eval show MetaM Unit from do
  --#--
  -- Create two fresh metavariables of type `Nat`.
  --#--
  -- `Nat` 型の新しいメタ変数を2つ作成する。
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)
  --#--
  -- Create a fresh metavariable of type `Nat → Nat`. The `mkArrow` function
  -- creates a function type.
  --#--
  -- `Nat → Nat` 型の新しいメタ変数を2つ作成する。`mkArrow` 関数は関数型を作ります。
  let mvar3 ← mkFreshExprMVar (← mkArrow (.const ``Nat []) (.const ``Nat []))
    (userName := `mvar3)

  --#--
  -- Define a helper function that prints each metavariable.
  --#--
  -- 各メタ変数を表示する補助関数を定義。
  let printMVars : MetaM Unit := do
    IO.println s!"  meta1: {← instantiateMVars mvar1}"
    IO.println s!"  meta2: {← instantiateMVars mvar2}"
    IO.println s!"  meta3: {← instantiateMVars mvar3}"

  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  --#--
  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  --#--
  -- `mvar1 : Nat := ?mvar3 ?mvar2` を割当。
  mvar1.mvarId!.assign (.app mvar3 mvar2)
  IO.println "After assigning mvar1:"
  printMVars

  --#--
  -- Assign `mvar2 : Nat := 0`.
  --#--
  -- `mvar2 : Nat := 0` を割当。
  mvar2.mvarId!.assign (.const ``Nat.zero [])
  IO.println "After assigning mvar2:"
  printMVars

  --#--
  -- Assign `mvar3 : Nat → Nat := Nat.succ`.
  --#--
  -- `mvar3 : Nat → Nat := Nat.succ` を割当。
  mvar3.mvarId!.assign (.const ``Nat.succ [])
  IO.println "After assigning mvar3:"
  printMVars
-- Initially, all metavariables are unassigned:
--   meta1: ?_uniq.1
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar1:
--   meta1: ?_uniq.3 ?_uniq.2
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar2:
--   meta1: ?_uniq.3 Nat.zero
--   meta2: Nat.zero
--   meta3: ?_uniq.3
-- After assigning mvar3:
--   meta1: Nat.succ Nat.zero
--   meta2: Nat.zero
--   meta3: Nat.succ


/-!
--#--
### Local Contexts

--#--
### ローカルコンテキスト

--#--
Consider the expression `e` which refers to the free variable with unique name
`h`:

--#--
一意な名前 `h` を参照している式 `e` について考えてみます：

```lean
e := .fvar (FVarId.mk `h)
```

--#--
What is the type of this expression? The answer depends on the local context in
which `e` is interpreted. One local context may declare that `h` is a local
hypothesis of type `Nat`; another local context may declare that `h` is a local
definition with value `List.map`.

--#--
この式の型は何でしょうか？この答えは `e`　が解釈されるローカルコンテキストに依存します。あるローカルコンテキストでは `h` は `Nat` 型のローカルの仮定かもしれません；また別のローカルコンテキストでは `List.map` の値を持つローカル定義として宣言されているかもしれません。

--#--
Thus, expressions are only meaningful if they are interpreted in the local
context for which they were intended. And as we saw, each metavariable has its
own local context. So in principle, functions which manipulate expressions
should have an additional `MVarId` argument specifying the goal in which the
expression should be interpreted.

--#--
したがって、式はそれが意図されたローカルコンテキストで解釈される場合にのみ意味を持ちます。そして先ほど見たように、各メタ変数はそれぞれ独自のローカルコンテキストを持っています。そのため原則的には、式を操作する関数には、その式の解釈を行うゴールを指定する `MVarId` 引数を追加する必要があります。

--#--
That would be cumbersome, so Lean goes a slightly different route. In `MetaM`,
we always have access to an ambient `LocalContext`, obtained with `Lean.getLCtx`
of type

--#--
これは面倒であるため、Leanでは少し異なる道を選んでいます。`MetaM` では常にそれを取り囲む `LocalContext` にアクセスすることができます。これは以下の型を持つ `Lean.getLCtx` から得られます。

```lean
getLCtx : MetaM LocalContext
```

--#--
All operations involving fvars use this ambient local context.

--#--
fvar を含むすべての操作は、この周囲のローカルコンテキストを使用します。

--#--
The downside of this setup is that we always need to update the ambient local
context to match the goal we are currently working on. To do this, we use
`Lean.MVarId.withContext` of type

--#--
この仕組みの欠点は、周囲のローカルコンテキストを現在取り組んでいるゴールに合わせて常に更新する必要があることです。これを行うには以下の型の `Lean.MVarId.withContext` を使います。

```lean
withContext (mvarId : MVarId) (c : MetaM α) : MetaM α
```

--#--
This function takes a metavariable `mvarId` and a `MetaM` computation `c` and
executes `c` with the ambient context set to the local context of `mvarId`. A
typical use case looks like this:

--#--
この関数はメタ変数 `mvarId` と `MetaM` の計算 `c` を取り、周囲のコンテキストを `mvarId` のローカルコンテキストに設定した上で `c` を実行します。典型的な使用例は以下のようになります：

```lean
def someTactic (mvarId : MVarId) ... : ... :=
  mvarId.withContext do
    ...
```

--#--
The tactic receives the current goal as the metavariable `mvarId` and
immediately sets the current local context. Any operations within the `do` block
then use the local context of `mvarId`.

--#--
このタクティクは現在のゴールをメタ変数 `mvarId` として受け取ると直ちに現在のローカルコンテキストを設定します。そして `do` ブロック内のすべての操作は `mvarId` のローカルコンテキストを使用します。

--#--
Once we have the local context properly set, we can manipulate fvars. Like
metavariables, fvars are identified by an `FVarId` (a unique `Name`). Basic
operations include:

--#--
ローカルコンテキストを適切に設定することで、fvar を操作することができます。メタ変数と同様に fvar は `FVarId` （一意な `Name`）で識別されます。基本的な操作は以下の通りです：

--#--
- `Lean.FVarId.getDecl : FVarId → MetaM LocalDecl` retrieves the declaration
  of a local hypothesis. As with metavariables, a `LocalDecl` contains all
  information pertaining to the local hypothesis, e.g. its type and its
  user-facing name.
- `Lean.Meta.getLocalDeclFromUserName : Name → MetaM LocalDecl` retrieves the
  declaration of the local hypothesis with the given user-facing name. If there
  are multiple such hypotheses, the bottommost one is returned. If there is
  none, an exception is thrown.

--#--
- `Lean.FVarId.getDecl : FVarId → MetaM LocalDecl` はローカルの仮定の宣言を取得します。メタ変数と同様に、 `LocalDecl` はローカルの仮定に関連するすべての情報、例えば型やユーザ向けの名前を含みます。
- `Lean.Meta.getLocalDeclFromUserName : Name → MetaM LocalDecl` は与えられたユーザ向けの名前を持つローカルの仮定の宣言を取得します。もし該当する仮定が複数ある場合は、一番下のものが返されます。無い場合は例外が投げられます。

--#--
We can also iterate over all hypotheses in the local context, using the `ForIn`
instance of `LocalContext`. A typical pattern is this:

--#--
また、`LocalContext` の `ForIn` インスタンスを使用して、ローカルコンテキスト内のすべての仮定に対して反復処理を行うこともできます。典型的なパターンは以下のようになります：

```lean
for ldecl in ← getLCtx do
  if ldecl.isImplementationDetail then
    continue
  --#--
  -- do something with the ldecl
  --#--
  -- ldecl について何か行う。
```

--#--
The loop iterates over every `LocalDecl` in the context. The
`isImplementationDetail` check skips local hypotheses which are 'implementation
details', meaning they are introduced by Lean or by tactics for bookkeeping
purposes. They are not shown to users and tactics are expected to ignore them.

--#--
このループはこのコンテキスト内のすべての `LocalDecl` を繰り返し処理します。`isImplementationDetail` によるチェックでは「実装の詳細」（これはLeanやタクティクによって記録目的で導入されたものを意味します）であるローカルの仮定はスキップされます。これらはユーザに表示されず、タクティクからは無視されることが期待されています。

--#--
At this point, we can build the `MetaM` part of an `assumption` tactic:
--#--
この時点で、`assumption` タクティクの `MetaM` 部分を構築することができます：
-/

def myAssumption (mvarId : MVarId) : MetaM Bool := do
  --#--
  -- Check that `mvarId` is not already assigned.
  --#--
  -- `mvarId` がすでに割当済みかどうかチェック。
  mvarId.checkNotAssigned `myAssumption
  --#--
  -- Use the local context of `mvarId`.
  --#--
  -- `mvarId` のローカルコンテキストを使用する。
  mvarId.withContext do
    --#--
    -- The target is the type of `mvarId`.
    --#--
    -- このターゲットは `mvarId` 型。
    let target ← mvarId.getType
    --#--
    -- For each hypothesis in the local context:
    --#--
    -- ローカルコンテキストの各仮定に対して：
    for ldecl in ← getLCtx do
      --#--
      -- If the hypothesis is an implementation detail, skip it.
      --#--
      -- もしこの仮定が実装の詳細であればスキップ。
      if ldecl.isImplementationDetail then
        continue
      --#--
      -- If the type of the hypothesis is definitionally equal to the target
      -- type:
      --#--
      -- もしこの仮定の型がターゲットの型と定義上等しい場合：
      if ← isDefEq ldecl.type target then
        --#--
        -- Use the local hypothesis to prove the goal.
        --#--
        -- このローカルの仮定をゴールの証明に使用する。
        mvarId.assign ldecl.toExpr
        --#--
        -- Stop and return true.
        --#--
        -- 処理を終了し、true を返す。
        return true
    --#--
    -- If we have not found any suitable local hypothesis, return false.
    --#--
    -- もし適したローカルの仮定が見つからなければ、false を返す。
    return false

/-
--#--
The `myAssumption` tactic contains three functions we have not seen before:

--#--
`myAssumption` タクティクにはこれまでに見たことのない3つの関数が含まれています：

--#--
- `Lean.MVarId.checkNotAssigned` checks that a metavariable is not already
  assigned. The 'myAssumption' argument is the name of the current tactic. It is
  used to generate a nicer error message.
- `Lean.Meta.isDefEq` checks whether two definitions are definitionally equal.
  See the [Definitional Equality section](#definitional-equality).
- `Lean.LocalDecl.toExpr` is a helper function which constructs the `fvar`
  expression corresponding to a local hypothesis.

--#--
- `Lean.MVarId.checkNotAssigned` はメタ変数がすでに割当済みかどうかチェックします。上記で渡している「myAssumption」引数は現在のタクティクの名前です。これはより良いエラーメッセージを生成するために使用されます。
- `Lean.Meta.isDefEq` は2つの定義が定義上等しいかどうかをチェックします。詳細は [定義上の同値の節](#definitional-equality) を参照してください。
- `Lean.LocalDecl.toExpr` はローカルの仮定に対応する `fvar` 式を構築する補助関数です。

--#--

### Delayed Assignments

--#--
### 遅延割当

--#--
The above discussion of metavariable assignment contains a lie by omission:
there are actually two ways to assign a metavariable. We have seen the regular
way; the other way is called a *delayed assignment*.

--#--
上記のメタ変数の割当についての議論にはあからさまな嘘が含まれていました：メタ変数の割当には本当は2つの方法があります。ここまででは正規の方法を見てきました；もう一つの方法は **遅延割当** （delayed assignment）と呼ばれます。

--#--
We do not discuss delayed assignments in any detail here since they are rarely
useful for tactic writing. If you want to learn more about them, see the
comments in `MetavarContext.lean` in the Lean standard library. But they create
two complications which you should be aware of.

--#--
遅延割当はタクティクの記述にはほとんど役に立たないので、ここでは詳しく説明しません。遅延割当について詳しく知りたいのであれば、Lean標準ライブラリの `MetavarContext.lean` のコメントを参照してください。しかし、遅延割当は2つの複雑な問題を引き起こすことを認識すべきです。

--#--
First, delayed assignments make `Lean.MVarId.isAssigned` and
`getExprMVarAssignment?` medium-calibre footguns. These functions only check for
regular assignments, so you may need to use `Lean.MVarId.isDelayedAssigned`
and `Lean.Meta.getDelayedMVarAssignment?` as well.

--#--
まず遅延割当によって、`Lean.MVarId.isAssigned` と `getExprMVarAssignment?` は自分の足を打ち抜く中口径の銃へと化します。これらの関数は通常の割当をチェックするだけであるため、`Lean.MVarId.isDelayedAssigned`
と `Lean.Meta.getDelayedMVarAssignment?` を使う必要があるでしょう。

--#--
Second, delayed assignments break an intuitive invariant. You may have assumed
that any metavariable which remains in the output of `instantiateMVars` is
unassigned, since the assigned metavariables have been substituted. But delayed
metavariables can only be substituted once their assigned value contains no
unassigned metavariables. So delayed-assigned metavariables can appear in an
expression even after `instantiateMVars`.

--#--
第二に、遅延割当は直観的な不変条件を破壊します。`instantiateMVars` の出力に残っているメタ変数は割り当てられていないと思われるかもしれません。というのも割り当てられたメタ変数は代入されるからです。しかし、遅延したメタ変数が代入されるのは、割り当てられた値に未割当のメタ変数が含まれていない場合のみです。そのため、`instantiateMVars` の後でも遅延割り当てられたメタ変数が式に現れることがあります。

--#--

### Metavariable Depth

--#--
### メタ変数の深さ

--#--
Metavariable depth is also a niche feature, but one that is occasionally useful.
Any metavariable has a *depth* (a natural number), and a `MetavarContext` has a
corresponding depth as well. Lean only assigns a metavariable if its depth is
equal to the depth of the current `MetavarContext`. Newly created metavariables
inherit the `MetavarContext`'s depth, so by default every metavariable is
assignable.

--#--
メタ変数の深さもニッチな機能ですが、時折役に立ちます。どのメタ変数も（自然数の） **深さ** （depth）を持ち、`MetavarContext` にも対応する深さがあります。Leanはメタ変数の深さが現在の `MetavarContext` の深さと等しい場合にのみメタ変数を割り当てます。新しく作成されたメタ変数は `MetavarContext` の深さを継承するため、デフォルトではすべてのメタ変数が割り当て可能です。

--#--
This setup can be used when a tactic needs some temporary metavariables and also
needs to make sure that other, non-temporary metavariables will not be assigned.
To ensure this, the tactic proceeds as follows:

--#--
この仕組みはタクティクが一時的なメタ変数を必要とし、かつ一時的でない他のメタ変数が割り当てられないようにする必要がある場合に使用できます。これを保証するために、タクティクは以下の順で処理します：

--#--
1. Save the current `MetavarContext`.
2. Increase the depth of the `MetavarContext`.
3. Perform whatever computation is necessary, possibly creating and assigning
   metavariables. Newly created metavariables are at the current depth of the
   `MetavarContext` and so can be assigned. Old metavariables are at a lower
   depth, so cannot be assigned.
4. Restore the saved `MetavarContext`, thereby erasing all the temporary
   metavariables and resetting the `MetavarContext` depth.

--#--
1. 現在の `MetavarContext` を保存する。
2. `MetavarContext` の深さを加算する。
3. 必要な計算を行い、場合によってはメタ変数を作成したり割り当てたりする。新しく作成されたメタ変数は `MetavarContext` の現在の深さにあるため割当を行うことができます。古いメタ変数の深さは浅いため、割り当てることができません。
4. 保存された `MetavarContext` を復元する。これにより、一時的なメタ変数がすべて消去され、`MetavarContext` の深さがリセットされます。

--#--
This pattern is encapsulated in `Lean.Meta.withNewMCtxDepth`.

--#--
このパターンは `Lean.Meta.withNewMCtxDepth` でカプセル化されています。

--#--

## Computation

--#--
## 計算

--#--
Computation is a core concept of dependent type theory. The terms `2`, `Nat.succ
1` and `1 + 1` are all "the same" in the sense that they compute the same value.
We call them *definitionally equal*. The problem with this, from a
metaprogramming perspective, is that definitionally equal terms may be
represented by entirely different expressions, but our users would usually
expect that a tactic which works for `2` also works for `1 + 1`. So when we
write our tactics, we must do additional work to ensure that definitionally
equal terms are treated similarly.

--#--
計算は依存型理論の核となる概念です。項 `2`・`Nat.succ 1`・`1 + 1` はすべて同じ値を計算するという意味で「同じ」です。これは **定義上等しい** （definitionally equal）と呼ばれます。メタプログラミングの観点からすると、これには定義上等しい項が全く異なる式で表現される可能性があるという問題が付随します。しかし、ユーザは通常、`2` に対して機能するタクティクは `1 + 1` に対しても機能することを期待するでしょう。そのため、タクティクを書くときには、定義上等しい項が同様に扱われるようにするための追加作業をしなければなりません。

--#--
### Full Normalisation

--#--
### 完全正規化

--#--
The simplest thing we can do with computation is to bring a term into normal
form. With some exceptions for numeric types, the normal form of a term `t` of
type `T` is a sequence of applications of `T`'s constructors. E.g. the normal
form of a list is a sequence of applications of `List.cons` and `List.nil`.

--#--
計算でできることの中で最も単純なものは項を正規形にすることです。数値型のいくつかの例外を除いて、`T` 型の項 `t` の正規形は `T` のコンストラクタの適用の列です。例えば、リストの正規形は `List.cons` と `List.nil` の適用の列です。

--#--
The function that normalises a term (i.e. brings it into normal form) is
`Lean.Meta.reduce` with type signature

--#--
項を正規化する（すなわち正規形にする）関数は `Lean.Meta.reduce` で、型シグネチャは以下の通りです。

```lean
reduce (e : Expr) (explicitOnly skipTypes skipProofs := true) : MetaM Expr
```

--#--
We can use it like this:
--#--
これは次のように使うことができます：
-/

def someNumber : Nat := (· + 2) $ 3

#eval Expr.const ``someNumber []
-- Lean.Expr.const `someNumber []

#eval reduce (Expr.const ``someNumber [])
-- Lean.Expr.lit (Lean.Literal.natVal 5)

/-!
--#--
Incidentally, this shows that the normal form of a term of type `Nat` is not
always an application of the constructors of `Nat`; it can also be a literal.
Also note that `#eval` can be used not only to evaluate a term, but also to
execute a `MetaM` program.

--#--
ちなみに、これは `Nat` 型の項の正規形が常に `Nat` のコンストラクタの適用であるとは限らないことを示しています；すなわち `Nat` はリテラルであることもあります。また、`#eval` は項を評価するだけでなく、`MetaM` プログラムを実行するためにも使用できます。

--#--
The optional arguments of `reduce` allow us to skip certain parts of an
expression. E.g. `reduce e (explicitOnly := true)` does not normalise any
implicit arguments in the expression `e`. This yields better performance: since
normal forms can be very big, it may be a good idea to skip parts of an
expression that the user is not going to see anyway.

--#--
`reduce` のオプション引数を使うことで、式の特定の部分をスキップすることができます。例えば、`reduce e (explicitOnly := true)` は式 `e` の暗黙の引数を正規化しません。これはパフォーマンスを改善します：正規形は非常に大きくなる可能性があるため、ユーザが見ることのない部分をスキップすることは良いアイデアになり得ます。

--#--
The `#reduce` command is essentially an application of `reduce`:
--#--
`#reduce` コマンドは本質的には `reduce` の適用です：
-/

#reduce someNumber
-- 5

/-!
--#--
### Transparency

--#--
### 透過度

--#--
An ugly but important detail of Lean 4 metaprogramming is that any given
expression does not have a single normal form. Rather, it has a normal form up
to a given *transparency*.

--#--
Lean4のメタプログラミングの醜いが重要な点は、任意の式がただ1つの正規形を持たないことです。その代わりに、所与の **透過度** （transparency）までの正規形を持ちます。

--#--
A transparency is a value of `Lean.Meta.TransparencyMode`, an enumeration with
four values: `reducible`, `instances`, `default` and `all`. Any `MetaM`
computation has access to an ambient `TransparencyMode` which can be obtained
with `Lean.Meta.getTransparency`.

--#--
透過度は `Lean.Meta.TransparencyMode` の値でこれは4つの値を持つ列挙型です：`reducible`・`instances`・`default`・`all`。どの `MetaM` の計算でも、周囲の `TransparencyMode` にアクセスすることができ、`Lean.Meta.getTransparency` で取得することができます。

--#--
The current transparency determines which constants get unfolded during
normalisation, e.g. by `reduce`. (To unfold a constant means to replace it with
its definition.) The four settings unfold progressively more constants:

--#--
現在の透過度は `reduce` などの正規化時にどの定数を展開するかを決定します。（定数の展開とは定数をその定義に置き換えるということを意味します。）4つの設定は段階的に多くの定数を展開します：

--#--
- `reducible`: unfold only constants tagged with the `@[reducible]` attribute.
  Note that `abbrev` is a shorthand for `@[reducible] def`.
- `instances`: unfold reducible constants and constants tagged with the
  `@[instance]` attribute. Again, the `instance` command is a shorthand for
  `@[instance] def`.
- `default`: unfold all constants except those tagged as `@[irreducible]`.
- `all`: unfold all constants, even those tagged as `@[irreducible]`.

--#--
- `reducible`：`@[reducible]` 属性でタグ付けされた定数のみを展開します。`abbrev` は `@[reducible] def` の省略形であることに注意してください。
- `instances`：`@[instance]` 属性でタグ付けされた定数や簡約可能な定数を展開します。ここでもまた、`instance` は `@[instance] def` の省略形です。
- `default`：`@[irreducible]` とタグ付けされた定数以外のすべての定数を展開します。
- `all`：`@[irreducible]` とタグ付けされたものも含めてすべての定数を展開します。

--#--
The ambient transparency is usually `default`. To execute an operation with a
specific transparency, use `Lean.Meta.withTransparency`. There are also
shorthands for specific transparencies, e.g. `Lean.Meta.withReducible`.

--#--
環境の透過度は通常 `default` です。特定の透過度で操作を実行するには `Lean.Meta.withTransparency` を使用します。また例えば `Lean.Meta.withReducible` などの特定の透過度に対する省略形もあります。

--#--
Putting everything together for an example (where we use `Lean.Meta.ppExpr` to
pretty-print an expression):
--#--
これらすべてを例にまとめます（ここでは式を綺麗に表示するために `Lean.Meta.ppExpr` を使用しています）：
-/

def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  ppExpr (← withTransparency md $ reduce (.const c []))

@[irreducible] def irreducibleDef : Nat      := 1
def                defaultDef     : Nat      := irreducibleDef + 1
abbrev             reducibleDef   : Nat      := defaultDef + 1

/-!
--#--
We start with `reducible` transparency, which only unfolds `reducibleDef`:
--#--
まず `reducibleDef` だけを展開する `reducible` から始めます：
-/

#eval traceConstWithTransparency .reducible ``reducibleDef
-- defaultDef + 1

/-!
--#--
If we repeat the above command but let Lean print implicit arguments as well,
we can see that the `+` notation amounts to an application of the `hAdd`
function, which is a member of the `HAdd` typeclass:
--#--
上記のコマンドを繰り返すだけでなく、Leanに暗黙の引数も表示させてみると、`+` の表記が `HAdd` 型クラスのメンバーである `hAdd` 関数の適用に相当することがわかります：
-/

set_option pp.explicit true
#eval traceConstWithTransparency .reducible ``reducibleDef
-- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) defaultDef 1

/-!
--#--
When we reduce with `instances` transparency, this applications is unfolded and
replaced by `Nat.add`:
--#--
`instances` の透過度で簡約する場合、この適用は展開され、`Nat.add` に置き換えられます：
-/

#eval traceConstWithTransparency .instances ``reducibleDef
-- Nat.add defaultDef 1

/-!
--#--
With `default` transparency, `Nat.add` is unfolded as well:
--#--
`default` 透過度では、`Nat.add` が以下のように展開されます：
-/

#eval traceConstWithTransparency .default ``reducibleDef
-- Nat.succ (Nat.succ irreducibleDef)

/-!
--#--
And with `TransparencyMode.all`, we're finally able to unfold `irreducibleDef`:
--#--
そして `TransparencyMode.all` で、ようやく `irreducibleDef` を展開できるようになります：
-/

#eval traceConstWithTransparency .all ``reducibleDef
-- 3

/-!
--#--
The `#eval` commands illustrate that the same term, `reducibleDef`, can have a
different normal form for each transparency.

--#--
この `#eval` コマンドは同じ項である `reducibleDef` がそれぞれの透過度に対して異なる正規形を持ちうることを表しています。

--#--
Why all this ceremony? Essentially for performance: if we allowed normalisation
to always unfold every constant, operations such as type class search would
become prohibitively expensive. The tradeoff is that we must choose the
appropriate transparency for each operation that involves normalisation.

--#--
なぜこのような仰々しい儀式が必要なのでしょうか？基本的にはパフォーマンスのためです：もし正規化が常にすべての定数を展開されるようになると、型クラス探索のような操作は法外に高価になります。このトレードオフは、正規化を含む各操作に対して適切な透過度を選択しなければならないということです。

--#--

### Weak Head Normalisation

--#--
### 弱頭正規化

--#--
Transparency addresses some of the performance issues with normalisation. But
even more important is to recognise that for many purposes, we don't need to
fully normalise terms at all. Suppose we are building a tactic that
automatically splits hypotheses of the type `P ∧ Q`. We might want this tactic
to recognise a hypothesis `h : X` if `X` reduces to `P ∧ Q`. But if `P`
additionally reduces to `Y ∨ Z`, the specific `Y` and `Z` do not concern us.
Reducing `P` would be unnecessary work.

--#--
透過度を確保することで、いくつかの正規化のパフォーマンス上の問題に対処できます。しかし、それ以上に重要なことは、多くの目的においては項を完全に正規化する必要は全くないことを認識することです。`P ∧ Q` 型の仮定を自動的に分割するタクティクを構築しようとしていると仮定しましょう。もし `X` が `P ∧ Q` に簡約されるなら、このタクティクは仮定 `h : X` を認識させたいと思うかもしれません。しかし、もし `P` がさらに `Y ∨ Z` に簡約されるとしても、この特定の `Y` と `Z` はこのタクティクには無関係です。`P` を簡約することは不必要な作業です。

--#--
This situation is so common that the fully normalising `reduce` is in fact
rarely used. Instead, the normalisation workhorse of Lean is `whnf`, which
reduces an expression to *weak head normal form* (WHNF).

--#--
このような状況は非常に一般的であるため、完全に正規化する `reduce` は実際にはほとんど使われません。その代わり、Leanの正規化の主力は `whnf` で、これは式を **弱頭正規形** （weak head normal form, WHNF）に簡約します。

--#--
Roughly speaking, an expression `e` is in weak-head normal form when it has the
form

--#--
大雑把に言えば、式 `e` が弱頭正規形であるのは、それが次のような形を取り、

```text
e = f x₁ ... xₙ   (n ≥ 0)
```

--#--
and `f` cannot be reduced (at the current transparency). To conveniently check
the WHNF of an expression, we define a function `whnf'`, using some functions
that will be discussed in the Elaboration chapter.
--#--
そして `f` が（現在の透過度では）簡約できない時です。式の WHNF を簡便にチェックするために、エラボレーションの章で説明するいくつかの関数を使って関数 `whnf'` を定義します。
-/

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)

/-!
--#--
Now, here are some examples of expressions in WHNF.

--#--
さて、ここから WHNF の式の例をいくつか挙げます。

--#--
Constructor applications are in WHNF (with some exceptions for numeric types):
--#--
（数値型においてはいくつかの例外がありますが）コンストラクタの適用は WHNF です：
-/

#eval whnf' `(List.cons 1 [])
-- [1]

/-!
--#--
The *arguments* of an application in WHNF may or may not be in WHNF themselves:
--#--
WHNF の適用の **引数** は WHNF そのものである場合とそうでない場合があります：
-/

#eval whnf' `(List.cons (1 + 1) [])
-- [1 + 1]

/-!
--#--
Applications of constants are in WHNF if the current transparency does not
allow us to unfold the constants:
--#--
定数の適用は、現在の透過度が定数を展開することを許可しない場合、WHNF になります：
-/

#eval withTransparency .reducible $ whnf' `(List.append [1] [2])
-- List.append [1] [2]

/-!
--#--
Lambdas are in WHNF:
--#--
ラムダ式は WHNF です：
-/

#eval whnf' `(λ x : Nat => x)
-- fun x => x

/-!
--#--
Foralls are in WHNF:
--#--
forall は WHNF です：
-/

#eval whnf' `(∀ x, x > 0)
-- ∀ (x : Nat), x > 0

/-!
--#--
Sorts are in WHNF:
--#--
ソートは WHNF です：
-/

#eval whnf' `(Type 3)
-- Type 3

/-!
--#--
Literals are in WHNF:
--#--
リテラルは WHNF です：
-/

#eval whnf' `((15 : Nat))
-- 15

/-!
--#--
Here are some more expressions in WHNF which are a bit tricky to test:

--#--
WHNF である式の中でも、確認がちょっと厄介なものをいくつか紹介しましょう：

```lean
?x 0 1  -- Assuming the metavariable `?x` is unassigned, it is in WHNF.
h 0 1   -- Assuming `h` is a local hypothesis, it is in WHNF.
```

--#--
On the flipside, here are some expressions that are not in WHNF.

--#--
逆に、WHNF ではない式をいくつか挙げましょう。

--#--
Applications of constants are not in WHNF if the current transparency allows us
to unfold the constants:
--#--
定数の適用は、もし現在の透過度によって定数を展開できるのであれば WHNF ではありません：
-/

#eval whnf' `(List.append [1])
-- fun x => 1 :: List.append [] x

/-!
--#--
Applications of lambdas are not in WHNF:
--#--
ラムダ式の適用は WHNF ではありません：
-/

#eval whnf' `((λ x y : Nat => x + y) 1)
-- `fun y => 1 + y`

/-!
--#--
`let` bindings are not in WHNF:
--#--
`let` 束縛は WHNF ではありません：
-/

#eval whnf' `(let x : Nat := 1; x)
-- 1

/-!
--#--
And again some tricky examples:

--#--
ここでまたいくつか厄介な例を挙げます：

```lean
?x 0 1 -- Assuming `?x` is assigned (e.g. to `Nat.add`), its application is not
          in WHNF.
h 0 1  -- Assuming `h` is a local definition (e.g. with value `Nat.add`), its
          application is not in WHNF.
```

--#--
Returning to the tactic that motivated this section, let us write a function
that matches a type of the form `P ∧ Q`, avoiding extra computation. WHNF
makes it easy:
--#--
本節の動機となったタクティクに戻り、余分な計算を割けて `P ∧ Q` という形の型にマッチする関数を書いてみましょう。WHNF であれば簡単です：
-/

def matchAndReducing (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) Q) => return some (P, Q)
  | _ => return none

/-
--#--
By using `whnf`, we ensure that if `e` evaluates to something of the form `P
∧ Q`, we'll notice. But at the same time, we don't perform any unnecessary
computation in `P` or `Q`.

--#--
`whnf` を使うことで、もし `e` が `P ∧ Q` のような形で評価されれば、それに気づくことができます。しかし、同時に `P` や `Q` で不必要な計算を行わないようにできます。

--#--
However, our 'no unnecessary computation' mantra also means that if we want to
perform deeper matching on an expression, we need to use `whnf` multiple times.
Suppose we want to match a type of the form `P ∧ Q ∧ R`. The correct way to do
this uses `whnf` twice:
--#--
しかし、「無駄な計算をしない」というお題目は、式に対してより深いマッチングを行いたい場合には `whnf` を複数回使う必要があることも意味しています。例えば、`P ∧ Q ∧ R` という型のマッチを行いたいとしましょう。これを行う正しい方法は `whnf` を使うことです：
-/

def matchAndReducing₂ (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) e') =>
    match ← whnf e' with
    | (.app (.app (.const ``And _) Q) R) => return some (P, Q, R)
    | _ => return none
  | _ => return none

/-!
--#--
This sort of deep matching up to computation could be automated. But until
someone builds this automation, we have to figure out the necessary `whnf`s
ourselves.

--#--
このくらいの計算までの深さのマッチであれば自動化できるかもしれません。しかし、誰かがこの自動化を構築するまでは、必要な `whnf` を自分で見つけ出さなければなりません。

--#--

### Definitional Equality

--#--
### 定義上の同値

--#--
As mentioned, definitional equality is equality up to computation. Two
expressions `t` and `s` are definitionally equal or *defeq* (at the current
transparency) if their normal forms (at the current transparency) are equal.

--#--
前述したように、定義上の同値は計算においての同値です。2つの式 `t` と `s` は（現在の透過度において）正規形が等しい場合、定義上等しい、もしくは **defeq** となります。

--#--
To check whether two expressions are defeq, use `Lean.Meta.isDefEq` with type
signature

--#--
2つの式が defeq であるかどうかをチェックするには、以下の型シグネチャを持つ `Lean.Meta.isDefEq` を使用します。

```lean
isDefEq : Expr → Expr → MetaM Bool
```

--#--
Even though definitional equality is defined in terms of normal forms, `isDefEq`
does not actually compute the normal forms of its arguments, which would be very
expensive. Instead, it tries to "match up" `t` and `s` using as few reductions
as possible. This is a necessarily heuristic endeavour and when the heuristics
misfire, `isDefEq` can become very expensive. In the worst case, it may have to
reduce `s` and `t` so often that they end up in normal form anyway. But usually
the heuristics are good and `isDefEq` is reasonably fast.

--#--
定義上の同値は正規形で定義されていますが、実際には `isDefEq` は非常に高価になりうる引数の正規形の計算をすることはありません。その代わりに、`t` と `s` をできるだけ少ない簡約で「一致」させようとします。これは必然的に発見的な試みであり、この発見的な試みが失敗すると `isDefEq` は非常に高価になる可能性があります。最悪の場合、`s` と `t` を頻繁に簡約しなければならず、結局正規形になってしまうこともあります。しかし、通常はこの発見的な手法はうまく働き、`isDefEq` はそれなりに高速です。

--#--
If expressions `t` and `u` contain assignable metavariables, `isDefEq` may
assign these metavariables to make `t` defeq to `u`. We also say that `isDefEq`
*unifies* `t` and `u`; such unification queries are sometimes written `t =?= u`.
For instance, the unification `List ?m =?= List Nat` succeeds and assigns `?m :=
Nat`. The unification `Nat.succ ?m =?= n + 1` succeeds and assigns `?m := n`.
The unification `?m₁ + ?m₂ + ?m₃ =?= m + n - k` fails and no metavariables are
assigned (even though there is a 'partial match' between the expressions).

--#--
式 `t` と `u` に割当可能なメタ変数が含まれている場合、`isDefEq` はこれらのメタ変数を代入して `t` と `u` に defeq となるようにすることができます。これは、`isDefEq` は `t` と `u` を **単一化** （unify）するとも言います；このようなユニフィケーションのクエリは `t =?= u` と書かれることもあります。例えば、ユニフィケーション `List ?m =?= List Nat` は成功し、`?m := Nat` を割り当てます。ユニフィケーション `Nat.succ ?m =?= n + 1` は成功し、`?m := n` を割り当てます。ユニフィケーション `?m₁ + ?m₂ + ?m₃ =?= m + n - k` は失敗し、メタ変数は（たとえ式の間に「部分一致」があっても）割り当てられません。

--#--
Whether `isDefEq` considers a metavariable assignable is determined by two
factors:

--#--
`isDefEq` がメタ変数を割り当て可能と見なすかどうかは、2つの要素によって決まります：

--#--
1. The metavariable's depth must be equal to the current `MetavarContext` depth.
   See the [Metavariable Depth section](#metavariable-depth).
2. Each metavariable has a *kind* (a value of type `MetavarKind`) whose sole
   purpose is to modify the behaviour of `isDefEq`. Possible kinds are:
   - Natural: `isDefEq` may freely assign the metavariable. This is the default.
   - Synthetic: `isDefEq` may assign the metavariable, but avoids doing so if
     possible. For example, suppose `?n` is a natural metavariable and `?s` is a
     synthetic metavariable. When faced with the unification problem
     `?s =?= ?n`, `isDefEq` assigns `?n` rather than `?s`.
   - Synthetic opaque: `isDefEq` never assigns the metavariable.

--#--
1. そのメタ変数の深さが現在の `MetavarContext` の深さと同じでなければならない。詳しくは [メタ変数の深さについての節](#metavariable-depth) を参照してください。
2. それぞれのメタ変数が `isDefEq` の動作を変更することだけが目的の **種** （kind、`MetavarKind` 型の値）を持つこと。可能な種は以下の通りです：
   - Natural：`isDefEq` はメタ変数を自由に割り当てます。これがデフォルトです。
   - Synthetic：`isDefEq` はメタ変数を割り当てることができますが、可能であれば割当を避けます。例えば、`?n` がnaturalなメタ変数で、`?s` がsyntheticなメタ変数であるとします。ユニフィケーションの問題 `?s =?= ?n` に直面したとき、`isDefEq` は `?s` ではなく `?n` に割当を行います。
   - Synthetic opaque：`isDefeq` はメタ変数に割当を決して行いません。

--#--

## Constructing Expressions

--#--
## 式の構築

--#--
In the previous chapter, we saw some primitive functions for building
expressions: `Expr.app`, `Expr.const`, `mkAppN` and so on. There is nothing
wrong with these functions, but the additional facilities of `MetaM` often
provide more convenient ways.

--#--
前の章では、式を構築するためにいくつかのプリミティブな関数を見ました：`Expr.app`・`Expr.const`・`mkAppN` などです。これらの関数に問題はありませんが、`MetaM` の追加機能によってより便利に提供されることが多いです。

--#--

### Applications

--#--
### 適用

--#--
When we write regular Lean code, Lean helpfully infers many implicit arguments
and universe levels. If it did not, our code would look rather ugly:
--#--
普通のLeanのコードを書くとき、Leanは多くの暗黙の引数や宇宙レベルを推論してくれます。もしそうしてくれなければ、我々のコードはかなり醜くなってしまうでしょう：
-/

def appendAppend (xs ys : List α) := (xs.append ys).append xs

set_option pp.all true in
set_option pp.explicit true in
#print appendAppend
-- def appendAppend.{u_1} : {α : Type u_1} → List.{u_1} α → List.{u_1} α → List.{u_1} α :=
-- fun {α : Type u_1} (xs ys : List.{u_1} α) => @List.append.{u_1} α (@List.append.{u_1} α xs ys) xs

/-!
--#--
The `.{u_1}` suffixes are universe levels, which must be given for every
polymorphic constant. And of course the type `α` is passed around everywhere.

--#--
接尾辞 `.{u_1}` は宇宙レベルであり、すべての多相な定数に与えなければなりません。そしてもちろん、この型 `α` はこの定義中のいたるところで渡されています。

--#--
Exactly the same problem occurs during metaprogramming when we construct
expressions. A hand-made expression representing the right-hand side of the
above definition looks like this:
--#--
メタプログラミングで式を組み立てる際にも、全く同じ問題が発生します。上記の定義の右辺の式を手作りすると次のようになります：
-/

def appendAppendRHSExpr₁ (u : Level) (α xs ys : Expr) : Expr :=
  mkAppN (.const ``List.append [u])
    #[α, mkAppN (.const ``List.append [u]) #[α, xs, ys], xs]

/-!
--#--
Having to specify the implicit arguments and universe levels is annoying and
error-prone. So `MetaM` provides a helper function which allows us to omit
implicit information: `Lean.Meta.mkAppM` of type

--#--
暗黙の引数や宇宙レベルを指定しなければならないのは煩わしく、エラーになりやすいです。そこで `MetaM` は暗黙的な情報を省略するための補助関数を提供しています：以下の型の `Lean.Meta.mkAppM` です。

```lean
mkAppM : Name → Array Expr → MetaM Expr
```

--#--
Like `mkAppN`, `mkAppM` constructs an application. But while `mkAppN` requires
us to give all universe levels and implicit arguments ourselves, `mkAppM` infers
them. This means we only need to provide the explicit arguments, which makes for
a much shorter example:
--#--
`mkAppN` と同様に、`mkAppM` は適用を構築します。しかし、`mkAppN` はすべての宇宙レベルと暗黙の引数を渡す必要があるのに対し、`mkAppM` はそれらを推測してくれます。つまり、明示的な引数を与えるだけでよいため、より短い例を作ってくれます：
-/

def appendAppendRHSExpr₂ (xs ys : Expr) : MetaM Expr := do
  mkAppM ``List.append #[← mkAppM ``List.append #[xs, ys], xs]

/-!
--#--
Note the absence of any `α`s and `u`s. There is also a variant of `mkAppM`,
`mkAppM'`, which takes an `Expr` instead of a `Name` as the first argument,
allowing us to construct applications of expressions which are not constants.

--#--
この例では `α` と `u` が一切ないことに注目してください。また `mkAppM` の変種として、第一引数に `Name` の代わりに `Expr` を取る `mkAppM'` があります。これによって定数ではない式の適用が可能になります。

--#--
However, `mkAppM` is not magic: if you write `mkAppM ``List.append #[]`, you
will get an error at runtime. This is because `mkAppM` tries to determine what
the type `α` is, but with no arguments given to `append`, `α` could be anything,
so `mkAppM` fails.

--#--
しかし、`mkAppM` は魔法ではありません：例えば `mkAppM ``List.append #[]` と書くと実行時エラーとなります。これは `mkAppM` が `α` 型が何であるか判断しようとしても、`append` に引数が与えられていないため `α` は何でも良いこととなり、`mkAppM` が失敗するからです。

--#--
Another occasionally useful variant of `mkAppM` is `Lean.Meta.mkAppOptM` of type

--#--
他の `mkAppM` の変種の中でしばしば便利であるのが、以下の型の `Lean.Meta.mkAppOptM` です。

```lean
mkAppOptM : Name → Array (Option Expr) → MetaM Expr
```

--#--
Whereas `mkAppM` always infers implicit and instance arguments and always
requires us to give explicit arguments, `mkAppOptM` lets us choose freely which
arguments to provide and which to infer. With this, we can, for example, give
instances explicitly, which we use in the following example to give a
non-standard `Ord` instance.
--#--
`mkAppM` が常に暗黙の引数とインスタンス引数を推論し、常に明示的な引数の提示を要求するのに対して、`mkAppOptM` ではどの引数を与え、どの引数を推論するのかを自由に選択することができます。これによって、例えばインスタンスを明示的に当てることができるようになり、以下の例のように標準ではない `Ord` インスタンスを渡すことが可能です。
-/

def revOrd : Ord Nat where
  compare x y := compare y x

def ordExpr : MetaM Expr := do
  mkAppOptM ``compare #[none, Expr.const ``revOrd [], mkNatLit 0, mkNatLit 1]

#eval format <$> ordExpr
-- Ord.compare.{0} Nat revOrd
--   (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
--   (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))

/-!
--#--
Like `mkAppM`, `mkAppOptM` has a primed variant `Lean.Meta.mkAppOptM'` which
takes an `Expr` instead of a `Name` as the first argument. The file which
contains `mkAppM` also contains various other helper functions, e.g. for making
list literals or `sorry`s.

--#--
`mkAppM` と同様に、`mkAppOptM` はプライムがついた版の `Lean.Meta.mkAppOptM'` があり、最初の引数として `Name` の代わりに `Expr` を取ります。`mkAppM` を定義しているファイルには、リストのリテラルや `sorry` を作成するための様々な補助関数も含まれています。

--#--

### Lambdas and Foralls

--#--
### ラムダ式と forall

--#--
Another common task is to construct expressions involving `λ` or `∀` binders.
Suppose we want to create the expression `λ (x : Nat), Nat.add x x`. One way is
to write out the lambda directly:
--#--
他の一般的なタスクとして、`λ` または `∀` 束縛子を含む式を作成することです。例えば、`λ (x : Nat), Nat.add x x` という式を作りたいとします。1つの方法はラムダ式を直接書き出すことです：
-/

def doubleExpr₁ : Expr :=
  .lam `x (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[.bvar 0, .bvar 0])
    BinderInfo.default

#eval ppExpr doubleExpr₁
-- fun x => Nat.add x x

/-!
--#--
This works, but the use of `bvar` is highly unidiomatic. Lean uses a so-called
*locally closed* variable representation. This means that all but the
lowest-level functions in the Lean API expect expressions not to contain 'loose
`bvar`s', where a `bvar` is loose if it is not bound by a binder in the same
expression. (Outside of Lean, such variables are usually called 'free'. The name
`bvar` -- 'bound variable' -- already indicates that `bvar`s are never supposed
to be free.)

--#--
これは機能しますが、この `bvar` の使い方は非常に単調です。Leanではいわゆる **locally closed** な変数表現を用います。つまり、Lean APIの最低レベルの関数を除いて、すべての関数で式が「loose な `bvar`」を含まないことを想定しています。ここで `bvar` が loose であるとは同じ式中で束縛子に束縛されないものを指すのでした。（Lean 以外では、このような変数は通常「自由（free）」と呼ばれます。`bvar`、すなわち「束縛変数」は `bvar` が決して自由でないことをその名前で示しています。）

--#--
As a result, if in the above example we replace `mkAppN` with the slightly
higher-level `mkAppM`, we get a runtime error. Adhering to the locally closed
convention, `mkAppM` expects any expressions given to it to have no loose bound
variables, and `.bvar 0` is precisely that.

--#--
その結果、上記の例で `mkAppN` を少しレベルの高い `mkAppM` に置き換えると、実行時エラーが発生します。locally closed の規約に従い、`mkAppM` は与えられた式に loose な束縛変数が無いことを期待しており、`.bvar 0` はまさにこれを満たします。

--#--
So instead of using `bvar`s directly, the Lean way is to construct expressions
with bound variables in two steps:

--#--
そこで、`bvar` を直接使う代わりに、Leanでは2つのステップで束縛変数を持つ式を構築する方針をとります：

--#--
1. Construct the body of the expression (in our example: the body of the
   lambda), using temporary local hypotheses (`fvar`s) to stand in for the bound
   variables.
2. Replace these `fvar`s with `bvar`s and, at the same time, add the
   corresponding lambda binders.

--#--
1. 一時的なローカルの仮定（`fvar`）を束縛変数の代わりに使い、式の本体（この例ではラムダ式の本体）を構築します。
2. これらの `fvar` を `bvar` に置き換え、同時に、これに対応するラムダ式の束縛子を追加します。

--#--
This process ensures that we do not need to handle expressions with loose
`bvar`s at any point (except during step 2, which is performed 'atomically' by a
bespoke function). Applying the process to our example:

--#--
この処理によって、loose な `bvar` を持つ式をどのタイミングにおいても扱う必要がなくなります（例外的にステップ2の間は特注の関数によって「アトミックに」実行されます）。このプロセスを例に当てはめると：
-/

def doubleExpr₂ : MetaM Expr :=
  withLocalDecl `x BinderInfo.default (.const ``Nat []) λ x => do
    let body ← mkAppM ``Nat.add #[x, x]
    mkLambdaFVars #[x] body

#eval show MetaM _ from do
  ppExpr (← doubleExpr₂)
-- fun x => Nat.add x x

/-!
--#--
There are two new functions. First, `Lean.Meta.withLocalDecl` has type

--#--
ここでは新しい関数が2つあります。まず、`Lean.Meta.withLocalDecl` は以下の型を持ちます。

```lean
withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → MetaM α) : MetaM α
```

--#--
Given a variable name, binder info and type, `withLocalDecl` constructs a new
`fvar` and passes it to the computation `k`. The `fvar` is available in the local
context during the execution of `k` but is deleted again afterwards.

--#--
変数名と束縛子の情報、型が与えられると、`withLocalDecl` は新しい `fvar` を作成して `k` の計算に渡します。`fvar` は `k` の実行中はローカルコンテキストで利用可能ですが、実行後に削除されます。

--#--
The second new function is `Lean.Meta.mkLambdaFVars` with type (ignoring some
optional arguments)

--#--
2つ目の新しい関数は `Lean.Meta.mkLambdaFVars` で、以下の型を持ちます（ここではいくつかのオプション引数を無視しています）。

```
mkLambdaFVars : Array Expr → Expr → MetaM Expr
```

--#--
This function takes an array of `fvar`s and an expression `e`. It then adds one
lambda binder for each `fvar` `x` and replaces every occurrence of `x` in `e`
with a bound variable corresponding to the new lambda binder. The returned
expression does not contain the `fvar`s any more, which is good since they
disappear after we leave the `withLocalDecl` context. (Instead of `fvar`s, we
can also give `mvar`s to `mkLambdaFVars`, despite its name.)

--#--
この関数は `fvar` の配列と式 `e` を取ります。そして各 `fvar` `x` に対してラムダの束縛子を1つずつ追加し、`e` 内で出現する `x` をすべて新しいラムダの束縛子に対応する束縛変数に置き換えます。こうして返される式は一切 `fvar` を含みません。`withLocalDecl` コンテキストを抜けると `fvar` は消えてしまうためこれは良いことです。（`fvar` の代わりに `mkLambdaFVars` に `mvar` を与えることもできます。）

--#--
Some variants of the above functions may be useful:

--#--
上記の関数のいくつかの変種が役に立つでしょう：

--#--
- `withLocalDecls` declares multiple temporary `fvar`s.
- `mkForallFVars` creates `∀` binders instead of `λ` binders. `mkLetFVars`
  creates `let` binders.
- `mkArrow` is the non-dependent version of `mkForallFVars` which construcs
  a function type `X → Y`. Since the type is non-dependent, there is no need
  for temporary `fvar`s.

--#--
- `withLocalDecls` は複数の一時的な `fvar` を宣言します。
- `mkForallFVars` は `λ` の束縛子の代わりに `∀` の束縛子を作成します。`mkLetFVars` は `let` の束縛子を作成します。
- `mkArrow` は `mkForallFVars` の非依存版で、関数型 `X → Y` を構築します。この型は非依存であるため、一時的な `fvar` は不要です。

--#--
Using all these functions, we can construct larger expressions such as this one:

--#--
これらの関数をすべて使えば、次のような大きな式を作ることができます：

```lean
λ (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)
```
-/

def somePropExpr : MetaM Expr := do
  let funcType ← mkArrow (.const ``Nat []) (.const ``Nat [])
  withLocalDecl `f BinderInfo.default funcType fun f => do
    let feqn ← withLocalDecl `n BinderInfo.default (.const ``Nat []) fun n => do
      let lhs := .app f n
      let rhs := .app f (← mkAppM ``Nat.succ #[n])
      let eqn ← mkEq lhs rhs
      mkForallFVars #[n] eqn
    mkLambdaFVars #[f] feqn

/-!
--#--
The next line registers `someProp` as a name for the expression we've just
constructed, allowing us to play with it more easily. The mechanisms behind this
are discussed in the Elaboration chapter.
--#--
次の例では、今作った式の名前として `someProp` を登録しており、より扱いやすくしています。このメカニズムについてはエラボレーションの章で説明します。
-/

elab "someProp" : term => somePropExpr

#check someProp
-- fun f => ∀ (n : Nat), f n = f (Nat.succ n) : (Nat → Nat) → Prop
#reduce someProp Nat.succ
-- ∀ (n : Nat), Nat.succ n = Nat.succ (Nat.succ n)


/-!
--#--
### Deconstructing Expressions

--#--
### 式の分解

--#--
Just like we can construct expressions more easily in `MetaM`, we can also
deconstruct them more easily. Particularly useful is a family of functions for
deconstructing expressions which start with `λ` and `∀` binders.

--#--
`MetaM` で式をより簡単に構築できるように、式をより簡単に分解することもできます。特に便利なのは、`λ` と `∀` の束縛子で始まる式を分解する関数群です。

--#--
When we are given a type of the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, we are
often interested in doing something with the conclusion `U`. For instance, the
`apply` tactic, when given an expression `e : ∀ ..., U`, compares `U` with the
current target to determine whether `e` can be applied.

--#--
`∀ (x₁ : T₁) ... (xₙ : Tₙ), U` という形式の型が与えられた時、たいていの場合は結論 `U` で何をするかということに興味があります。例えば、`apply` タクティクは `e : ∀ ..., U` という式が与えられた時、`U` と現在のターゲットを比較し、`e` が適用できるかどうかを判断します。

--#--
To do this, we could repeatedly match on the type expression, removing `∀`
binders until we get to `U`. But this would leave us with an `U` containing
unbound `bvar`s, which, as we saw, is bad. Instead, we use
`Lean.Meta.forallTelescope` of type

--#--
これを行うには、`U` にたどり着くまで `∀` の束縛子を取り除きながら型の式のマッチを繰り返せば良いです。しかし、これでは束縛されてない `bvar` を含んだ `U` が残ってしまい、これは見てきたようにまずいです。その代わりに、以下の型の `Lean.Meta.forallTelescope` を使用します。

```
forallTelescope (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α
```

--#--
Given `type = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U x₁ ... xₙ`, this function creates one
fvar `fᵢ` for each `∀`-bound variable `xᵢ` and replaces each `xᵢ` with `fᵢ` in
the conclusion `U`. It then calls the computation `k`, passing it the `fᵢ` and
the conclusion `U f₁ ... fₙ`. Within this computation, the `fᵢ` are registered
in the local context; afterwards, they are deleted again (similar to
`withLocalDecl`).

--#--
`type = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U x₁ ... xₙ` が与えられると、この関数は各 `∀` の束縛変数 `xᵢ` に対して fvar `fᵢ` を1つずつ作成し、結論 `U` の各 `xᵢ` を `fᵢ` で置換します。次に、`fᵢ` と結論 `U f₁ ... fₙ` を渡して計算 `k` を呼び出します。この計算の中で、`fᵢ` はローカルコンテキストに登録されます；最終的に、これらは削除されます（`withLocalDecl` と同様です）。

--#--
There are many useful variants of `forallTelescope`:

--#--
`forallTelescope` には便利なバリエーションがたくさんあります：

--#--
- `forallTelescopeReducing`: like `forallTelescope` but matching is performed up
  to computation. This means that if you have an expression `X` which is
  different from but defeq to `∀ x, P x`, `forallTelescopeReducing X` will
  deconstruct `X` into `x` and `P x`. The non-reducing `forallTelescope` would
  not recognise `X` as a quantified expression. The matching is performed by
  essentially calling `whnf` repeatedly, using the ambient transparency.
- `forallBoundedTelescope`: like `forallTelescopeReducing` (even though there is
  no "reducing" in the name) but stops after a specified number of `∀` binders.
- `forallMetaTelescope`, `forallMetaTelescopeReducing`,
  `forallMetaBoundedTelescope`: like the corresponding non-`meta` functions, but
  the bound variables are replaced by new `mvar`s instead of `fvar`s. Unlike the
  non-`meta` functions, the `meta` functions do not delete the new metavariables
  after performing some computation, so the metavariables remain in the
  environment indefinitely.
- `lambdaTelescope`, `lambdaTelescopeReducing`, `lambdaBoundedTelescope`,
  `lambdaMetaTelescope`: like the corresponding `forall` functions, but for
  `λ` binders instead of `∀`.

--#--
- `forallTelescopeReducing`：これは `forallTelescope` と似ていますが、マッチが計算にまで実行されます。つまり、`∀ x, P x` と異なるが defeq である式 `X` がある時、`forallTelescopeReducing X` は `X` を `x` と `P x` に分解します。これに対し非簡約的な `forallTelescope` は `X` を量化された式とは認識しません。このマッチは基本的に周囲の透過度を使用して `whnf` を繰り返し呼び出すことで行われます。
- `forallBoundedTelescope`：これは `forallTelescopeReducing` と（名前に「reducing」が入っていませんが）似ていますが、これはマッチを指定した数分の `∀` 束縛子の後に停止します。
- `forallMetaTelescope`・`forallMetaTelescopeReducing`・`forallMetaBoundedTelescope`：これらはそれぞれ対応する非 `meta` 版の関数と似ていますが、ここでの束縛変数は `fvar` の代わりに新しい `mvar` に置換されます。非 `meta` 版の関数とは異なり、この `meta` 版の関数は計算を行った後に新しいメタ変数を削除しないため、メタ変数は無期限に環境に残り続けます。
- `lambdaTelescope`・`lambdaTelescopeReducing`・`lambdaBoundedTelescope`・`lambdaMetaTelescope`：これらは対応する `forall` 関数と似ていますが、`∀` の代わりに `λ` の束縛子を対象にしています。

--#--
Using one of the telescope functions, we can implement our own `apply` tactic:
--#--
テレスコープ関数の1つを使って、独自の `apply` タクティクを実装することができます：
-/

def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  --#--
  -- Check that the goal is not yet assigned.
  --#--
  -- ゴールが未割当かどうかチェックする。
  goal.checkNotAssigned `myApply
  --#--
  -- Operate in the local context of the goal.
  --#--
  -- このゴールのローカルコンテキストで操作を行う。
  goal.withContext do
    --#--
    -- Get the goal's target type.
    --#--
    -- ゴールのターゲットの型を取得。
    let target ← goal.getType
    --#--
    -- Get the type of the given expression.
    --#--
    -- 与えられた式の型を取得。
    let type ← inferType e
    --#--
    -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
    -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `type` does
    -- not have this form, `args` is empty and `conclusion = type`.)
    --#--
    -- `type` が `∀ (x₁ : T₁) ... (xₙ : Tₙ), U` の形式を持つ場合、`xᵢ` に対応する新しいメタ変数を導入し、この結論 `U` を取得する。（もし `type` がこの形式でない場合、`args` は空で `conclusion = type`　となる。）
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    --#--
    -- If the conclusion unifies with the target:
    --#--
    -- この結論がこのターゲットを単一化する場合：
    if ← isDefEq target conclusion then
      --#--
      -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
      -- metavariables in `args`.
      --#--
      -- ゴールに `e x₁ ... xₙ` を割り当てる。ここで `xᵢ` は `args` の中の新鮮なメタ変数。
      goal.assign (mkAppN e args)
      --#--
      -- `isDefEq` may have assigned some of the `args`. Report the rest as new
      -- goals.
      --#--
      -- `isDefEq` は `args` の中のいくつかのメタ変数を割り当てるかもしれないため、その結果残った新しいゴールを報告する。
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    --#--
    -- If the conclusion does not unify with the target, throw an error.
    --#--
    -- この結論がターゲットを単一化しない場合、例外を投げる。
    else
      throwTacticEx `myApply goal m!"{e} is not applicable to goal with target {target}"

/-!
--#--
The real `apply` does some additional pre- and postprocessing, but the core
logic is what we show here. To test our tactic, we need an elaboration
incantation, more about which in the Elaboration chapter.
--#--
実際の `apply` はいくつかの追加の前処理と後処理を行いますが、核となるロジックはここで紹介したものです。このタクティクをテストするには、エラボレーションの呪文が必要です。詳しくはエラボレーションの章で説明します。
-/

elab "myApply" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (myApply · e)

example (h : α → β) (a : α) : β := by
  myApply h
  myApply a


/-!
--#--
## Backtracking

--#--
## バックトラッキング

--#--
Many tactics naturally require backtracking: the ability to go back to a
previous state, as if the tactic had never been executed. A few examples:

--#--
多くのタクティクはバックトラッキングを当然のものとして必要とします：これは以前の状態へ戻る能力で、あたかもそのタクティクが実行されていなかったかのようになります。いくつか例を挙げましょう：

--#--
- `first | t | u` first executes `t`. If `t` fails, it backtracks and executes
  `u`.
- `try t` executes `t`. If `t` fails, it backtracks to the initial state,
  erasing any changes made by `t`.
- `trivial` attempts to solve the goal using a number of simple tactics
  (e.g. `rfl` or `contradiction`). After each unsuccessful application of such a
  tactic, `trivial` backtracks.

--#--
- `first | t | u` はまず `t` を実行します。もし `t` が失敗したら、バックトラックして `u` を実行します。
- `try t` は `t` を実行します。もし `t` が失敗したら、初期状態へとバックトラックし、 `t` による変更を消去します。
- `trivial` はいくつかのシンプルなタクティク（例えば `rfl` や `contradiction`）を使用してゴールを解こうとします。これらのタクティクの適用が成功しなかった場合、`trivial` はバックトラックします。

--#--
Good thing, then, that Lean's core data structures are designed to enable easy
and efficient backtracking. The corresponding API is provided by the
`Lean.MonadBacktrack` class. `MetaM`, `TermElabM` and `TacticM` are all
instances of this class. (`CoreM` is not but could be.)

--#--
良いことに、Leanのコアデータ構造は簡単かつ効率的なバックトラックができるように設計されています。対応する API は `Lean.MonadBacktrack` クラスで提供されます。`MetaM`・`TermElabM`・`TacticM` はすべてこのクラスのインスタンスです。（`CoreM` はそうではありませんが、そうなる可能性があります。）

--#--
`MonadBacktrack` provides two fundamental operations:

--#--
`MonadBacktrack` は2つの基礎的な操作を提供しています：

--#--
- `Lean.saveState : m s` returns a representation of the current state, where
  `m` is the monad we are in and `s` is the state type. E.g. for `MetaM`,
  `saveState` returns a `Lean.Meta.SavedState` containing the current
  environment, the current `MetavarContext` and various other pieces of
  information.
- `Lean.restoreState : s → m Unit` takes a previously saved state and restores
  it. This effectively resets the compiler state to the previous point.

--#--
- `Lean.saveState : m s` は現在の状態の表現を返します。ここで `m` は利用しているモナドで、`s` は状態の型です。例えば `MetaM` の場合、`saveState` は現在の環境、現在の `MetavarContext` とその他様々な情報を含む `Lean.Meta.SavedState` を返します。
- `Lean.restoreState : s → m Unit` は以前に保存された状態を取り出し、復元します。これは効率的にコンパイラの状態を前の時点のものにリセットします。

--#--
With this, we can roll our own `MetaM` version of the `try` tactic:
--#--
これによって、`try` タクティクの `MetaM` バージョンを独自に開発することができます：
-/

def tryM (x : MetaM Unit) : MetaM Unit := do
  let s ← saveState
  try
    x
  catch _ =>
    restoreState s

/-!
--#--
We first save the state, then execute `x`. If `x` fails, we backtrack the state.

--#--
まず状態を保存し、次に `x` を実行します。もし `x` が失敗したら状態をバックトラックします。

--#--
The standard library defines many combinators like `tryM`. Here are the most
useful ones:

--#--
標準ライブラリには `tryM` のようなコンビネータがたくさん定義されています。ここでは最も便利なものを紹介します：

--#--
- `Lean.withoutModifyingState (x : m α) : m α` executes the action `x`, then
  resets the state and returns `x`'s result. You can use this, for example, to
  check for definitional equality without assigning metavariables:
  ```lean
  withoutModifyingState $ isDefEq x y
  ```
  If `isDefEq` succeeds, it may assign metavariables in `x` and `y`. Using
  `withoutModifyingState`, we can make sure this does not happen.
- `Lean.observing? (x : m α) : m (Option α)` executes the action `x`. If `x`
  succeeds, `observing?` returns its result. If `x` fails (throws an exception),
  `observing?` backtracks the state and returns `none`. This is a more
  informative version of our `tryM` combinator.
- `Lean.commitIfNoEx (x : α) : m α` executes `x`. If `x` succeeds,
  `commitIfNoEx` returns its result. If `x` throws an exception, `commitIfNoEx`
  backtracks the state and rethrows the exception.

--#--
- `Lean.withoutModifyingState (x : m α) : m α` はアクション `x` を実行し、状態をリセットして `x` の結果を返します。これは例えばメタ変数を代入せずに定義が等しいかどうかをチェックするために使うことができます：
  ```lean
  withoutModifyingState $ isDefEq x y
  ```
  もし `isDefEq` が成功すると、`x` と `y` にメタ変数が割り当てられる可能性があります。`withoutModifyingState` を使えば、このようなことが起こらないようにすることができます。
- `Lean.observing? (x : m α) : m (Option α)` はアクション `x` を実行します。`x` が成功すると、`observing?` はその結果を返します。`x` が失敗した場合（例外を投げた場合）、`observing?` は状態をバックトラックして `none` を返します。これは `tryM` コンビネータのより情報量に富んだバージョンです。
- `Lean.commitIfNoEx (x : α) : m α` は `x` を実行します。`x` が成功すると、`commitIfNoEx` はその結果を返します。`x` が例外を投げた場合、`commitIfNoEx` は状態をバックトラックして例外を投げ直します。

--#--
Note that the builtin `try ... catch ... finally` does not perform any
backtracking. So code which looks like this is probably wrong:

--#--
ここで組み込みの `try ... catch ... finally` はバックトラックを行わないことに注意してください。したがって、次のようなコードはおそらく間違っています：

```lean
try
  doSomething
catch e =>
  doSomethingElse
```

--#--
The `catch` branch, `doSomethingElse`, is executed in a state containing
whatever modifications `doSomething` made before it failed. Since we probably
want to erase these modifications, we should write instead:

--#--
`catch` の枝の `doSomethingElse` は、`doSomething` が失敗する前に行った変更を含む状態で実行されます。これらの変更を消去したいはずであるので、代わりにこのように書くべきです：

```lean
try
  commitIfNoEx doSomething
catch e =>
  doSomethingElse
```

--#--
Another `MonadBacktrack` gotcha is that `restoreState` does not backtrack the
*entire* state. Caches, trace messages and the global name generator, among
other things, are not backtracked, so changes made to these parts of the state
are not reset by `restoreState`. This is usually what we want: if a tactic
executed by `observing?` produces some trace messages, we want to see them even
if the tactic fails. See `Lean.Meta.SavedState.restore` and `Lean.Core.restore`
for details on what is and is not backtracked.

--#--
もう一つの `MonadBacktrack` の欠点は、`restoreState` は状態 **全体** をバックトラックしないことです。キャッシュ・トレースメッセージ・グローバル名のジェネレータなどはバックトラックされないため、これらの部分に加えられた変更は `restoreState` でリセットされません。これは通常望ましいことです：`observing?` によって実行されたタクティクがトレースメッセージを生成した場合、そのタクティクが失敗してもトレースメッセージを見ることができます。バックトラックされるものと、されないものの詳細については、`Lean.Meta.SavedState.restore` と `Lean.Core.restore` を参照してください。

--#--
In the next chapter, we move towards the topic of elaboration, of which
you've already seen several glimpses in this chapter. We start by discussing
Lean's syntax system, which allows you to add custom syntactic constructs to the
Lean parser.

--#--
次の章では、この章ですでに何度か垣間見たエラボレーションの話題に移ります。まずLeanの構文システムについて説明します。このシステムではLeanのパーサにカスタムの構文を追加することができます。

--#--
## Exercises

--#--
## 演習問題

--#--
1. [**Metavariables**] Create a metavariable with type `Nat`, and assign to it value `3`.
Notice that changing the type of the metavariable from `Nat` to, for example, `String`, doesn't raise any errors - that's why, as was mentioned, we must make sure *"(a) that `val` must have the target type of `mvarId` and (b) that `val` must only contain `fvars` from the local context of `mvarId`"*.
2. [**Metavariables**] What would `instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])` output?
3. [**Metavariables**] Fill in the missing lines in the following code.

--#--
1. [**メタ変数**] `Nat` 型のメタ変数を作成し、値 `3` を割り当ててください。ここでメタ変数の型を `Nat` から例えば `String` に変更してもエラーにならないことに注してください。そのため前述の通り、「(a) その `val` が `mvarId` のターゲットの型を持ち、(b) `val` が `mvarId` のローカルコンテキストにある `fvarId` しか含まないこと」を確認する必要があります。
2. [**メタ変数**] `instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])` は何を出力するでしょうか？
3. [**メタ変数**] 以下のコードの欠けている行を埋めてください。

    ```lean
    #eval show MetaM Unit from do
      let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
      let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

      -- Create `mvar1` with type `Nat`
      -- let mvar1 ← ...
      -- Create `mvar2` with type `Nat`
      -- let mvar2 ← ...
      -- Create `mvar3` with type `Nat`
      -- let mvar3 ← ...

      -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
      -- ...

      -- Assign `mvar3` to `1`
      -- ...

      -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
      ...
    ```
--#--
4. [**Metavariables**] Consider the theorem `red`, and tactic `explore` below.
  **a)** What would be the `type` and `userName` of metavariable `mvarId`?
  **b)** What would be the `type`s and `userName`s of all local declarations in this metavariable's local context?
  Print them all out.

--#--
4. [**メタ変数**] 下記の定理 `red` とタクティク `explore` について考えてみましょう。
  **a)** メタ変数 `mvarId` の `type` と `userName` は何になるでしょうか？
  **b)** このメタ変数のローカルコンテキストにあるすべてのローカル宣言の `type` と `userName` は何になるでしょうか？それらをすべて表示させてください。

    ```lean
    elab "explore" : tactic => do
      let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
      let metavarDecl : MetavarDecl ← mvarId.getDecl

      IO.println "Our metavariable"
      -- ...

      IO.println "All of its local declarations"
      -- ...

    theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
      explore
      sorry
    ```
--#--
5. [**Metavariables**] Write a tactic `solve` that proves the theorem `red`.
6. [**Computation**] What is the normal form of the following expressions:
  **a)** `fun x => x` of type `Bool → Bool`
  **b)** `(fun x => x) ((true && false) || true)` of type `Bool`
  **c)** `800 + 2` of type `Nat`
7. [**Computation**] Show that `1` created with `Expr.lit (Lean.Literal.natVal 1)` is definitionally equal to an expression created with `Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])`.
8. [**Computation**] Determine whether the following expressions are definitionally equal. If `Lean.Meta.isDefEq` succeeds, and it leads to metavariable assignment, write down the assignments.
  **a)** `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`
  **b)** `2 + 1 =?= 1 + 2`
  **c)** `?a =?= 2`, where `?a` has a type `String`
  **d)** `?a + Int =?= "hi" + ?b`, where `?a` and `?b` don't have a type
  **e)** `2 + ?a =?= 3`
  **f)** `2 + ?a =?= 2 + 1`
9. [**Computation**] Write down what you expect the following code to output.

--#--
5. [**メタ変数**] 上記の定理 `red` を証明するタクティク `solve` を書いてください。
6. [**計算**] 以下の式の正規形は何になるでしょうか？
  **a)** `Bool → Bool` 型の `fun x => x`
  **b)** `Bool` 型の `(fun x => x) ((true && false) || true)`
  **c)** `Nat` 型の `800 + 2`
7. [**計算**] `Expr.lit (Lean.Literal.natVal 1)` で作られた `1` と `Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])` で作られた式が定義上等しいことを示してください。
8. [**計算**] 以下の式が定義上等しいかどうか判定してください。もし `Lean.Meta.isDefEq` が成功し、メタ変数の割り当てを導くなら、その割当も書き下してください。
  **a)** `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`
  **b)** `2 + 1 =?= 1 + 2`
  **c)** `?a =?= 2`、ここで `?a` は `String` 型
  **d)** `?a + Int =?= "hi" + ?b`、ここで `?a` と `?b` は型を持ちません
  **e)** `2 + ?a =?= 3`
  **f)** `2 + ?a =?= 2 + 1`
9. [**計算**] 次のコードが何を出力することを期待するか書き下してください。

    ```lean
    @[reducible] def reducibleDef     : Nat := 1 -- same as `abbrev`
    @[instance] def instanceDef       : Nat := 2 -- same as `instance`
    def defaultDef                    : Nat := 3
    @[irreducible] def irreducibleDef : Nat := 4

    @[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

    #eval show MetaM Unit from do
      let constantExpr := Expr.const `sum []

      Meta.withTransparency Meta.TransparencyMode.reducible do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      Meta.withTransparency Meta.TransparencyMode.instances do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      Meta.withTransparency Meta.TransparencyMode.default do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      Meta.withTransparency Meta.TransparencyMode.all do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      let reducedExpr ← Meta.reduce constantExpr
      dbg_trace (← ppExpr reducedExpr) -- ...
    ```
--#--
10. [**Constructing Expressions**] Create expression `fun x, 1 + x` in two ways:
  **a)** not idiomatically, with loose bound variables
  **b)** idiomatically.
  In what version can you use `Lean.mkAppN`? In what version can you use `Lean.Meta.mkAppM`?
11. [**Constructing Expressions**] Create expression `∀ (yellow: Nat), yellow`.
12. [**Constructing Expressions**] Create expression `∀ (n : Nat), n = n + 1` in two ways:
  **a)** not idiomatically, with loose bound variables
  **b)** idiomatically.
  In what version can you use `Lean.mkApp3`? In what version can you use `Lean.Meta.mkEq`?
13. [**Constructing Expressions**] Create expression `fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)` idiomatically.
14. [**Constructing Expressions**] What would you expect the output of the following code to be?

--#--
10. [**式の構築**] 式 `fun x, 1 + x` を2通りで構築してください：
  **a)** loose な束縛変数を含んだ単調な方法
  **b)** 便利な関数を用いる方法
  `Lean.mkAppN` はどちらのバージョンで使用できるでしょうか？また、`Lean.Meta.mkAppM` はどちらのバージョンで使用できるでしょうか？
11. [**式の構築**] 式 `∀ (yellow: Nat), yellow` を構築してください。
12. [**式の構築**] 式 `∀ (n : Nat), n = n + 1` を2通りで構築してください：
  **a)** loose な束縛変数を含んだ単調な方法
  **b)** 便利な関数を用いる方法
  `Lean.mkApp3` はどちらのバージョンで使用できるでしょうか？また、`Lean.Meta.mkEq` はどちらのバージョンで使用できるでしょうか？
13. [**式の構築**] 式 `fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)` を便利な関数を用いる方法で構築してください。
14. [**式の構築**] 次のコードの出力はどうなるでしょうか？

    ```lean
    #eval show Lean.Elab.Term.TermElabM _ from do
      let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
      let expr ← Elab.Term.elabTermAndSynthesize stx none

      let (_, _, conclusion) ← forallMetaTelescope expr
      dbg_trace conclusion -- ...

      let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
      dbg_trace conclusion -- ...

      let (_, _, conclusion) ← lambdaMetaTelescope expr
      dbg_trace conclusion -- ...
    ```
--#--
15. [**Backtracking**] Check that the expressions `?a + Int` and `"hi" + ?b` are definitionally equal with `isDefEq` (make sure to use the proper types or `Option.none` for the types of your metavariables!).
Use `saveState` and `restoreState` to revert metavariable assignments.
--#--
15. [**バックトラッキング**] `isDefEq` を使用して `?a + Int` と `"hi" + ?b` が定義上等しいことをチェックしてください（メタ変数の型には適切な型、または `Option.none` を使用してください！）。メタ変数の割り当てを戻すには、`saveState` と `restoreState` を使用してください。
-/
