/-
--#--
# Expressions

--#--
# 式

--#--
Expressions (terms of type `Expr`) are an abstract syntax tree for Lean programs.
This means that each term which can be written in Lean has a corresponding `Expr`.
For example, the application `f e` is represented by the expression `Expr.app ⟦f⟧ ⟦e⟧`,
where `⟦f⟧` is a representation of `f` and `⟦e⟧` a representation of `e`.
Similarly, the term `Nat` is represented by the expression ``Expr.const `Nat []``.
(The backtick and empty list are discussed below.)

--#--
式（`Expr` 型の項）はLeanプログラムの抽象構文木です。つまり、Leanで記述される各項には対応する `Expr` があります。例えば、関数適用 `f e` は式 `Expr.app ⟦f⟧ ⟦e⟧` で表現されます。ここで `⟦f⟧` は `f` の表現であり、`⟦e⟧` は `e` の表現です。同様に、`Nat` という項は ``Expr.const `Nat []`` という式で表されます。（バッククォートと空リストについては後述します。）

--#--
The ultimate purpose of a Lean tactic block
is to generate a term which serves as a proof of the theorem we want to prove.
Thus, the purpose of a tactic is to produce (part of) an `Expr` of the right type.
Much metaprogramming therefore comes down to manipulating expressions:
constructing new ones and taking apart existing ones.

--#--
Leanのタクティクブロックの最終的な目的は証明したい定理の証明となる項を生成することです。つまり、タクティクの目的は正しい型（の一部）の `Expr` を生成することです。したがって、メタプログラミングの多くは式を操作することに帰着します：新しい項を構成したり、既存の項を分解したりします。

--#--
Once a tactic block is finished, the `Expr` is sent to the kernel,
which checks whether it is well-typed and whether it really has the type claimed by the theorem.
As a result, tactic bugs are not fatal:
if you make a mistake, the kernel will ultimately catch it.
However, many internal Lean functions also assume that expressions are well-typed,
so you may crash Lean before the expression ever reaches the kernel.
To avoid this, Lean provides many functions which help with the manipulation of expressions.
This chapter and the next survey the most important ones.

--#--
タクティクブロックが終了すると、`Expr` はカーネルに送られます。カーネルはこの項がきちんと型付けされているか、定理が主張する型を本当に持っているかをチェックします。結果として、タクティクのバグは致命的なものにはなりません：もしミスがあっても、最終的にはカーネルがそれをキャッチしてくれます。しかし、多くのLeanの内部関数も式がきちんと型付けされていることを仮定しているため、式がカーネルに到達する前にLeanがクラッシュする可能性があります。これを避けるためにLeanは式の操作を支援する多くの関数を提供しています。この章と次の章では最も重要なものを調査します。

--#--
Let's get concrete and look at the
[`Expr`](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)
type:
--#--
[`Expr`](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean) の型について実際のものを見てみましょう：
-/

import Lean

namespace Playground

inductive Expr where
  | bvar    : Nat → Expr                              -- bound variables
  | fvar    : FVarId → Expr                           -- free variables
  | mvar    : MVarId → Expr                           -- meta variables
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- constants
  | app     : Expr → Expr → Expr                      -- application
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda abstraction
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- (dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                          -- literals
  | mdata   : MData → Expr → Expr                     -- metadata
  | proj    : Name → Nat → Expr → Expr                -- projection

end Playground

/-!
--#--
What is each of these constructors doing?

--#--
それぞれのコンストラクタは何をするのでしょうか？

--#--
- `bvar` is a __bound variable__.
  For example, the `x` in `fun x => x + 2` or `∑ x, x²`.
  This is any occurrence of a variable in an expression where there is a binder above it.
  Why is the argument a `Nat`? This is called a de Bruijn index and will be explained later.
  You can figure out the type of a bound variable by looking at its binder,
  since the binder always has the type information for it.
- `fvar` is a __free variable__.
  These are variables which are not bound by a binder.
  An example is `x` in `x + 2`.
  Note that you can't just look at a free variable `x` and tell what its type is,
  there needs to be a context which contains a declaration for `x` and its type.
  A free variable has an ID that tells you where to look for it in a `LocalContext`.
  In Lean 3, free variables were called "local constants" or "locals".
- `mvar` is a __metavariable__.
  There will be much more on these later,
  but you can think of it as a placeholder or a 'hole' in an expression
  that needs to be filled at a later point.
- `sort` is used for `Type u`, `Prop` etc.
- `const` is a constant that has been defined earlier in the Lean document.
- `app` is a function application.
  Multiple arguments are done using _partial application_: `f x y ↝ app (app f x) y`.
- `lam n t b` is a lambda expression (`fun ($n : $t) => $b`).
  The `b` argument is called the __body__.
  Note that you have to give the type of the variable you are binding.
- `forallE n t b` is a dependent arrow expression (`($n : $t) → $b`).
  This is also sometimes called a Π-type or Π-expression
  and is often written `∀ $n : $t, $b`.
  Note that the non-dependent arrow `α → β` is a special case of `(a : α) → β`
  where `β` doesn't depend on `a`.
  The `E` on the end of `forallE` is to distinguish it from the `forall` keyword.
- `letE n t v b` is a __let binder__ (`let ($n : $t) := $v in $b`).
- `lit` is a __literal__, this is a number or string literal like `4` or `"hello world"`.
  Literals help with performance:
  we don't want to represent the expression `(10000 : Nat)`
  as `Nat.succ $ ... $ Nat.succ Nat.zero`.
- `mdata` is just a way of storing extra information on expressions that might be useful,
  without changing the nature of the expression.
- `proj` is for projection.
  Suppose you have a structure such as `p : α × β`,
  rather than storing the projection `π₁ p` as `app π₁ p`, it is expressed as `proj Prod 0 p`.
  This is for efficiency reasons ([todo] find link to docstring explaining this).

--#--
- `bvar` は **束縛変数** （bound variable）です。例えば、`fun x => x + 2` や `∑ x, x²` などにおいての `x` です。これはある変数について、それの上に束縛子（binder）がいる場合のその式中での変数の出現を表します。なぜ引数は `Nat` なのでしょうか？これはde Bruijnインデックスと呼ばれるもので、後で説明します。束縛変数の型はその束縛子を見ればわかります。というのも束縛子は常にその変数の型の情報を持っているからです。
- `fvar` は **自由変数** （free variable）です。これは束縛子で束縛されていない変数のことです。自由変数 `x` について、それを見ても型が何であるか知ることができないことに注意してください。型を知るには `x` とその型の宣言を含むコンテキストが必要です。自由変数にはIDがあり、これはその変数を `LocalContext` のどこを探せばよいかを教えてくれます。Lean 3では、自由変数は「ローカル変数」または「ローカル」と呼ばれていました。
- `mvar` は **メタ変数** （metavariable）です。これについては後ほど詳しく説明しますが、プレースホルダや、後で埋める必要のある表現のための「穴」と考えてもらえれば良いです。
- `sort` は `Type u` や `Prop` などで使われます。
- `const` はLeanの記述中でそこまでに定義済みの定数です。
- `app` は関数適用です。複数の引数の場合は **部分適用** （partial application）を用います：`f x y ↝ app (app f x) y`。
- `lam n t b` はラムダ式（`fun ($n : $t) => $b`）です。引数 `b` は **本体** （body）と呼ばれます。束縛する変数の型を指定する必要がある点に注意してください。
- `forallE n t b` は依存矢印式（`($n : $t) → $b`）です。これはΠ型、もしくはΠ式とも呼ばれ、しばしば `∀ $n : $t, $b` と書かれます。依存しない矢印 `α → β` は `β` が `a` に依存しない `(a : α) → β` の特殊な場合であることに注意してください。`forallE` の末尾の `E` は `forall` キーワードと区別するためのものです。
- `letE n t v b` は **let束縛子** （let binder）です（`let ($n : $t) := $v in $b`）。
- `lit` は **リテラル** （literal）で、これは `4` や `"hello world"` などの数値や文字列のリテラルです。リテラルはパフォーマンスを向上させることに役立ちます：式 `(10000 : Nat)` を `Nat.succ $ ... $ Nat.succ Nat.zero` のように表現したくはありません。
- `mdata` は式の性質を変えることなく、式に役立つかもしれない追加の情報を保存するためだけのものです。
- `proj` は射影を表します。`p : α × β` のような構造体があるとすると、射影 `π₁ p` を `app π₁ p` として格納するのではなく、`proj Prod 0 p` と表現します。これは効率化のためです。

--#--
You've probably noticed
that you can write many Lean programs which do not have an obvious corresponding `Expr`.
For example, what about `match` statements, `do` blocks or `by` blocks?
These constructs, and many more, must indeed first be translated into expressions.
The part of Lean which performs this (substantial) task is called the elaborator
and is discussed in its own chapter.
The benefit of this setup is that once the translation to `Expr` is done,
we have a relatively simple structure to work with.
(The downside is that going back from `Expr` to a high-level Lean program can be challenging.)

--#--
おそらく読者は明らかに対応する `Expr` を持たない多くのLeanプログラムを書くことができることに気付いているでしょう。例えば、`match` 文や `do` ブロック、`by` ブロックはどうすればいいのでしょうか？これらの構文やその他多くの構文はまず式に変換する必要があります。Leanにおいてこの（実質的な）タスクを実行する部分はエラボレータと呼ばれ、それ用の章で説明します。この構成の利点は、いったん `Expr` への変換が終われば、比較的単純な構造で作業ができることです。（欠点は `Expr` から高レベルのLeanプログラムに戻るのが難しいことです。）

--#--
The elaborator also fills in any implicit or typeclass instance arguments
which you may have omitted from your Lean program.
Thus, at the `Expr` level, constants are always applied to all their arguments, implicit or not.
This is both a blessing
(because you get a lot of information which is not obvious from the source code)
and a curse
(because when you build an `Expr`, you must supply any implicit or instance arguments yourself).

--#--
エラボレータはまた、読者がLeanのプログラムで省略した暗黙の引数や型クラスのインスタンス引数も埋めます。このように `Expr` レベルでは暗黙的であろうとなかろうと、定数は常にすべての引数に適用されます。これは祝福（というのもソースコードでは明確でなかった多くの情報を得ることができるからです）であり、また呪い（`Expr` を組み立てる時に暗黙の引数やインスタンス引数を自分で指定しなければならないからです）でもあります。

--#--
## De Bruijn Indexes

--#--
## De Bruijn インデックス

--#--
Consider the following lambda expression `(λ f x => f x x) (λ x y => x + y) 5`,
we have to be very careful when we reduce this,
because we get a clash in the variable `x`.

--#--
次のラムダ式 `(λ f x => f x x) (λ x y => x + y) 5` を考えてみると、変数 `x` が衝突しているため、これを簡約する際には細心の注意を払う必要があります。

--#--
To avoid variable name-clash carnage,
`Expr`s use a nifty trick called __de Bruijn indexes__.
In de Bruijn indexing,
each variable bound by a `lam` or a `forallE` is converted into a number `#n`.
The number says how many binders up the `Expr` tree we should look
to find the binder which binds this variable.
So our above example would become
(putting wildcards `_` in the type arguments for now for brevity):
``app (app (lam `f _ (lam `x _ (app (app #1 #0) #0))) (lam `x _ (lam `y _ (app (app plus #1) #0)))) five``
Now we don't need to rename variables when we perform β-reduction.
We also really easily check if two `Expr`s containing bound expressions are equal.
This is why the signature of the `bvar` case is `Nat → Expr` and not `Name → Expr`.

--#--
変数名の衝突を避けるために、`Expr` では **de Bruijnインデックス** と呼ばれる巧妙な技法を使用します。de Bruijnインデックスにおいて、`lam` や `forallE` で束縛された各変数は `#n` という数値に変換されます。この数字は、この変数を束縛している束縛子を見つけるために `Expr` ツリーの何番目の束縛子を探せばよいかを示しています。そのため、上記の例は次のようになります（簡潔にするために型引数にはワイルドカード `_` を入れています）：``app (app (lam `f _ (lam `x _ (app (app #1 #0) #0))) (lam `x _ (lam `y _ (app (app plus #1) #0)))) five``。これでβ簡約を実行する際に変数名を変更する必要がなくなります。また、束縛された式を含む2つの `Expr` が等しいかどうかも簡単にチェックできます。これが `bvar` のシグネチャが `Name → Expr` ではなく `Nat → Expr` である理由です。

--#--
If a de Bruijn index is too large for the number of binders preceding it,
we say it is a __loose `bvar`__;
otherwise we say it is __bound__.
For example, in the expression ``lam `x _ (app #0 #1)``
the `bvar` `#0` is bound by the preceding binder and `#1` is loose.
The fact that Lean calls all de Bruijn indexes `bvar`s ("bound variables")
points to an important invariant:
outside of some very low-level functions,
Lean expects that expressions do not contain any loose `bvar`s.
Instead, whenever we would be tempted to introduce a loose `bvar`,
we immediately convert it into an `fvar` ("free variable").
Precisely how that works is discussed in the next chapter.

--#--
もしde Bruijnインデックスがそこまでに定義された束縛子の数よりも大きすぎる場合、**loose `bvar`** と言います；そうでない場合は **束縛されている** と言います。例えば、式 ``lam `x _ (app #0 #1)`` では、`bvar` `#0` は先行する束縛子によって束縛され、`#1` はlooseです。Leanがすべてのde Bruijnインデックスを `bvar` （「束縛変数」）と呼んでいる事実は重要な不変性を示しています：いくつかの低レベルな関数以外では、Leanはすべての式がlooseな `bvar` を含まないことを期待しています。一方でlooseな `bvar` を導入したい場合は、直ちに `fvar` （「自由変数」）に変換します。この具体的な方法については次の章で説明します。

--#--
If there are no loose `bvar`s in an expression, we say that the expression is __closed__.
The process of replacing all instances of a loose `bvar` with an `Expr`
is called __instantiation__.
Going the other way is called __abstraction__.

--#--
式の中にlooseな `bvar` が無い場合、その式は **閉じている** （closed）と言います。looseな `bvar` のインスタンスをすべて `Expr` に置き換えるプロセスは **インスタンス化** （instantiation）と呼びます。その逆は **抽象化** （abstraction）と呼ばれます。

--#--
If you are familiar with the standard terminology around variables,
Lean's terminology may be confusing,
so here's a map:
Lean's "bvars" are usually called just "variables";
Lean's "loose" is usually called "free";
and Lean's "fvars" might be called "local hypotheses".

--#--
もし読者が変数にまつわる標準的な用語に慣れているならLeanの用語は混乱するかもしれないので、ここで対応を挙げます：Leanでの「bvar」は通常単に「変数」と呼ばれます；「loose」は通常「自由」と呼ばれます；「fvar」は「ローカルな仮定」と呼ばれることがあります。

--#--
## Universe Levels

--#--
## 宇宙レベル

--#--
Some expressions involve universe levels, represented by the `Lean.Level` type.
A universe level is a natural number,
a universe parameter (introduced with a `universe` declaration),
a universe metavariable or the maximum of two universes.
They are relevant for two kinds of expressions.

--#--
いくつかの式は `Lean.Level` 型で表される宇宙レベルを含みます。宇宙レベルは自然数であり、宇宙パラメータ（`universe` 宣言で導入されます）、宇宙メタ変数、または2つの宇宙の最大値となります。これらは2種類の式の表現に関連します。

--#--
First, sorts are represented by `Expr.sort u`, where `u` is a `Level`.
`Prop` is `sort Level.zero`; `Type` is `sort (Level.succ Level.zero)`.

--#--
まず、ソートは `Expr.sort u` で表現されます。ここで `u` は `Level` です。`Prop` は `sort Level.zero` です；`Type` は `sort (Level.succ Level.zero)` です。

--#--
Second, universe-polymorphic constants have universe arguments.
A universe-polymorphic constant is one whose type contains universe parameters.
For example, the `List.map` function is universe-polymorphic,
as the `pp.universes` pretty-printing option shows:
--#--
次に、宇宙多相な定数は宇宙引数を持ちます。宇宙多相な定数とは宇宙パラメータを持つ型のことです。例えば、`pp.universe` オプションによる整形表示が示すように、`List.map` 関数は宇宙多相です：
-/

set_option pp.universes true in
#check @List.map

/-!
--#--
The `.{u_1,u_2}` suffix after `List.map`
means that `List.map` has two universe arguments, `u_1` and `u_2`.
The `.{u_1}` suffix after `List` (which is itself a universe-polymorphic constant)
means that `List` is applied to the universe argument `u_1`, and similar for `.{u_2}`.

--#--
`List.map` の接尾辞 `.{u_1,u_2}` は `List.map` が2つの宇宙引数 `u_1` と `u_2` を持つことを意味します。`List` の後の接尾辞 `.{u_1}` （これ自体が宇宙多相な定数）は `List` が宇宙引数 `u_1` に適用されることを意味し、`.{u_2}` についても同様です。

--#--
In fact, whenever you use a universe-polymorphic constant,
you must apply it to the correct universe arguments.
This application is represented by the `List Level` argument of `Expr.const`.
When we write regular Lean code, Lean infers the universes automatically,
so we do not need think about them much.
But when we construct `Expr`s,
we must be careful to apply each universe-polymorphic constant to the right universe arguments.

--#--
実は、宇宙多相な定数を使うときは必ず正しい宇宙引数に適用しなければなりません。この適用は `Expr.const` の `List Level` 引数で表現されます。通常のLeanコードを書くとき、Leanは自動的に宇宙を推論するため、あまり考える必要はありません。しかし、自力で `Expr` を構築する際には、それぞれの宇宙多相な定数を正しい宇宙引数に適用するように注意しなければなりません。

--#--
## Constructing Expressions

--#--
## 式の構築

--#--
### Constants

--#--
### 定数

--#--
The simplest expressions we can construct are constants.
We use the `const` constructor and give it a name and a list of universe levels.
Most of our examples only involve non-universe-polymorphic constants,
in which case the list is empty.

--#--
もっとも単純な式は定数です。これにあたってはコンストラクタ `const` を使い、名前と宇宙レベルのリストを与えます。ここでのほとんどの例では宇宙多相ではない定数のみを使用しており、この場合リストは空になります。

--#--
We also show a second form where we write the name with double backticks.
This checks that the name in fact refers to a defined constant,
which is useful to avoid typos.
--#--
また2つのバッククォートで名前を記述する第二の形式も示します。これは名前が実際に定義された定数を指しているかどうかをチェックするもので、タイプミスを避けるにあたって便利です。
-/

open Lean

def z' := Expr.const `Nat.zero []
#eval z' -- Lean.Expr.const `Nat.zero []

def z := Expr.const ``Nat.zero []
#eval z -- Lean.Expr.const `Nat.zero []

/-
--#--
The double-backtick variant also resolves the given name, making it fully-qualified.
To illustrate this mechanism, here are two further examples.
The first expression, `z₁`, is unsafe:
if we use it in a context where the `Nat` namespace is not open,
Lean will complain that there is no constant called `zero` in the environment.
In contrast, the second expression, `z₂`,
contains the fully-qualified name `Nat.zero` and does not have this problem.
--#--
また、バッククォート2つバージョンは与えられた名前を解決し、完全に修飾します。このメカニズムを説明するために、さらに2つの例を挙げましょう。1つ目の式 `z₁` は安全ではありません：もし `Nat` 名前空間が開かれていないコンテキストで使用すると Leanは環境に `zero` という定数が無いと文句を言います。対照的に、2番目の式 `z₂` は完全修飾名 `Nat.zero` を含んでおり、この問題はありません。
-/

open Nat

def z₁ := Expr.const `zero []
#eval z₁ -- Lean.Expr.const `zero []

def z₂ := Expr.const ``zero []
#eval z₂ -- Lean.Expr.const `Nat.zero []

/-
--#--
### Function Applications

--#--
### 関数適用

--#--
The next class of expressions we consider are function applications.
These can be built using the `app` constructor,
with the first argument being an expression for the function
and the second being an expression for the argument.

--#--
次に考える式の話題は関数適用です。これらは `app` コンストラクタを使って構築することができ、第1引数には関数の式を、第2引数には引数の式を指定します。

--#--
Here are two examples.
The first is simply a constant applied to another.
The second is a recursive definition giving an expression as a function of a natural number.
--#--
ここでは2つの例を挙げます。ひとつは単純に定数を別の定数に適用したものです。もう一つは式を自然数の関数として与える再帰的定義です。
-/

def one := Expr.app (.const ``Nat.succ []) z
#eval one
-- Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero [])

def natExpr: Nat → Expr
| 0     => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

/-
--#--
Next we use the variant `mkAppN` which allows application with multiple arguments.
--#--
次では、複数の引数を持つ適用を可能にする `mkAppN` を用いています。
-/

def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]

/-
--#--
As you may have noticed, we didn't show `#eval` outputs for the two last functions.
That's because the resulting expressions can grow so large
that it's hard to make sense of them.

--#--
お気づきかもしれませんが、最後の2つの関数については `#eval` の出力を示しませんでした。これは結果の式が大きくなりすぎて意味を理解するのが難しいからです。

--#--
### Lambda Abstractions

--#--
### ラムダ抽象

--#--
We next use the constructor `lam`
to construct a simple function which takes any natural number `x` and returns `Nat.zero`.
The argument `BinderInfo.default` says that `x` is an explicit argument
(rather than an implicit or typeclass argument).
--#--
次にコンストラクタ `lam` を使って、任意の自然数を受け取って `Nat.zero` を返す単純な関数を作成します。引数の `BinderInfo.default` は `x` が（暗黙の引数や型クラスの引数ではなく）明示的な引数であることを表しています。
-/

def constZero : Expr :=
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default

#eval constZero
-- Lean.Expr.lam `x (Lean.Expr.const `Nat []) (Lean.Expr.const `Nat.zero [])
--   (Lean.BinderInfo.default)

/-!
--#--
As a more elaborate example which also involves universe levels,
here is the `Expr` that represents `List.map (λ x => Nat.add x 1) []`
(broken up into several definitions to make it somewhat readable):
--#--
宇宙レベルに絡んだより込み入った例として、以下の `Expr` は　`List.map (λ x => Nat.add x 1) []` を表します（多少読みやすくするためにいくつかの定義に分割しています）：
-/

def nat : Expr := .const ``Nat []

def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelZero, levelZero])
    #[nat, nat, addOne, .app (.const ``List.nil [levelZero]) nat]

/-!
--#--
With a little trick (more about which in the Elaboration chapter),
we can turn our `Expr` into a Lean term, which allows us to inspect it more easily.
--#--
ちょっとした技法を使えば（詳しくはエラボレーションの章で）、この `Expr` をLeanの項にして、より簡単に検査できるようにすることができます。
-/

elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil
-- List.map (fun x => Nat.add x 1) [] : List Nat

set_option pp.universes true in
set_option pp.explicit true in
#check mapAddOneNil
-- @List.map.{0, 0} Nat Nat (fun x => x.add 1) (@List.nil.{0} Nat) : List.{0} Nat

#reduce mapAddOneNil
-- []

/-
--#--
In the next chapter we explore the `MetaM` monad,
which, among many other things,
allows us to more conveniently construct and destruct larger expressions.

--#--
次の章では、`MetaM` モナドを探求します。このモナドは多くのほかのモナドの中において、より大きな式をより便利に構築・分解できるようにします。

--#--
## Exercises

--#--
## 演習問題

--#--
1. Create expression `1 + 2` with `Expr.app`.
2. Create expression `1 + 2` with `Lean.mkAppN`.
3. Create expression `fun x => 1 + x`.
4. [**De Bruijn Indexes**] Create expression `fun a, fun b, fun c, (b * a) + c`.
5. Create expression `fun x y => x + y`.
6. Create expression `fun x, String.append "hello, " x`.
7. Create expression `∀ x : Prop, x ∧ x`.
8. Create expression `Nat → String`.
9. Create expression `fun (p : Prop) => (λ hP : p => hP)`.
10. [**Universe levels**] Create expression `Type 6`.
--#--
1. 式 `1 + 2` を `Expr.app` で作ってください。
2. 式 `1 + 2` を `Lean.mkAppN` で作ってください。
3. 式 `fun x => 1 + x` を作ってください
4. [**de Bruijn インデックス**] 式 `fun a, fun b, fun c, (b * a) + c` を作ってください。
5. 式 `fun x y => x + y` を作ってください。
6. 式 `fun x, String.append "hello, " x` を作ってください。
7. 式 `∀ x : Prop, x ∧ x` を作ってください。
8. 式 `Nat → String` を作ってください。
9. 式 `fun (p : Prop) => (λ hP : p => hP)` を作ってください。
10. [**宇宙レベル**] 式 `Type 6` を作ってください。
-/
