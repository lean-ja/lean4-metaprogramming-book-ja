/-
--#--
# Macros

--#--
# マクロ

--#--
## What is a macro
--#--
## マクロとは
--#--
Macros in Lean are `Syntax → MacroM Syntax` functions. `MacroM` is the macro
monad which allows macros to have some static guarantees we will discuss in the
next section, you can mostly ignore it for now.

--#--
Lean においてのマクロとは `Syntax → MacroM Syntax` である関数のことです。`MacroM` はマクロのためのモナドで、次節で説明する静的な保証をマクロに持たせることができますが、現時点ではおおむね無視しても構いません。

--#--
Macros are registered as handlers for a specific syntax declaration using the
`macro` attribute. The compiler will take care of applying these function
to the syntax for us before performing actual analysis of the input. This
means that the only thing we have to do is declare our syntax with a specific
name and bind a function of type `Lean.Macro` to it. Let's try to reproduce
the `LXOR` notation from the `Syntax` chapter:
--#--
マクロの登録は `macro` 属性を使用して、特定の構文宣言のハンドラとすることで行われます。コンパイラはこうして入力されたものに対して実際の解析を行う前に、これらの関数に構文の適用を行ってくれます。したがって利用者がすべきことは構文を特定の名前で宣言し、 `Lean.Macro` 型の関数をそれにバインドするだけです。`Syntax` の章の `LXOR` 記法を再現してみましょう：
-/

import Lean

open Lean

syntax:10 (name := lxor) term:10 " LXOR " term:11 : term

@[macro lxor] def lxorImpl : Macro
  | `($l:term LXOR $r:term) => `(!$l && $r) -- we can use the quotation mechanism to create `Syntax` in macros
  | _ => Macro.throwUnsupported

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/-
--#--
That was quite easy! The `Macro.throwUnsupported` function can be used by a macro
to indicate that "it doesn't feel responsible for this syntax". In this case
it's merely used to fill a wildcard pattern that should never be reached anyways.

--#--
とても簡単です！マクロが `Macro.throwUnsupported` 関数を使用すると、「この構文が管理されていないようである」ことを示すことができます。今回の場合、単に絶対に到達しないワイルドカードのパターンを埋めるために使用されています。

--#--
However we can in fact register multiple macros for the same syntax this way
if we desire, they will be tried one after another (the later registered ones have
higher priority)  -- is "higher" correct?
until one throws either a real error using `Macro.throwError` or succeeds, that
is it does not `Macro.throwUnsupported`. Let's see this in action:
--#--
しかし、実はその気になれば同じ構文に対して複数のマクロを登録することも可能であり、その場合は各マクロが次々に試行されます（後に登録されたものほど優先度が高くなります。この「高さ」は正しい？）。この試行は、どれかが `Macro.throwError` を使用して実際のエラー、つまり `Macro.throwUnsupported` によるもの以外を投げるか成功するまで続けられます。
-/

@[macro lxor] def lxorImpl2 : Macro
  --#--
  -- special case that changes behaviour of the case where the left and
  -- right hand side are these specific identifiers
  --#--
  -- 左右の識別子が特定の場合のケースの挙動を変更するための特殊ケース
  | `(true LXOR true) => `(true)
  | _ => Macro.throwUnsupported

#eval true LXOR true -- true, handled by new macro
#eval true LXOR false -- false, still handled by the old

/-
--#--
This capability is obviously *very* powerful! It should not be used
lightly and without careful thinking since it can introduce weird
behaviour while writing code later on. The following example illustrates
this weird behaviour:
--#--
この機能は明らかに **あまりにも** 強力です！これは後でコードを追加した際に奇妙な挙動を引き起こす可能性があるため、軽い気持ちで使ってはならず、慎重に考えるべきです。次の例は、この奇妙な挙動を示しています：
-/

#eval true LXOR true -- true, handled by new macro

def foo := true
#eval foo LXOR foo -- false, handled by old macro, after all the identifiers have a different name

/-
--#--
Without knowing exactly how this macro is implemented this behaviour
will be very confusing to whoever might be debugging an issue based on this.
The rule of thumb for when to use a macro vs. other mechanisms like
elaboration is that as soon as you are building real logic like in the 2nd
macro above, it should most likely not be a macro but an elaborator
(explained in the elaboration chapter). This means ideally we want to
use macros for simple syntax to syntax translations, that a human could
easily write out themselves as well but is too lazy to.

--#--
このマクロがどのように実装されているかを正確に知らなければ、この動作に基づいて問題をデバッグする人は非常に混乱するでしょう。マクロの使用とエラボレーションのような他のメカニズムの使用の使い分けの経験則として、上記の2番目のマクロのように実際のロジックを構築する場合はマクロではなくエラボレータを使用することをお勧めします（エラボレーションの章で説明します）。つまり理想的にはマクロは、人間が手でも簡単に書き出せるがあまりにもめんどくさいような構文から構文へのシンプルな変換のために用いたいのです。

--#--
## Simplifying macro declaration
--#--
## 簡略化されたマクロ宣言
--#--
Now that we know the basics of what a macro is and how to register it
we can take a look at slightly more automated ways to do this (in fact
all of the ways about to be presented are implemented as macros themselves).

--#--
ここまででマクロとは何か、マクロを登録する方法などの基本がわかったところで、もう少し自動化された方法を見てみましょう（実は、これから紹介する方法はすべてマクロとして実装されています）。

--#--
First things first there is `macro_rules` which basically desugars to
functions like the ones we wrote above, for example:
--#--
まず最初に `macro_rules` というものがあり、これは基本的に、例えば上記で書いたような関数に脱糖します：
-/

syntax:10 term:10 " RXOR " term:11 : term

macro_rules
  | `($l:term RXOR $r:term) => `($l && !$r)

/-
--#--
As you can see, it figures out lot's of things on its own for us:
- the name of the syntax declaration
- the `macro` attribute registration
- the `throwUnsupported` wildcard

--#--
見てわかる通り、これはさまざまなことをかわりに行ってくれます：
- 構文宣言の名前
- `macro` 属性の登録
- `throwUnsupported` ワイルドカード

--#--
apart from this it just works like a function that is using pattern
matching syntax, we can in theory encode arbitrarily complex macro
functions on the right hand side.

--#--
これを除けば、この構文はまさにパターンマッチ構文を使った関数のように動作し、理論的には右手側に任意の複雑なマクロ関数をエンコードすることができます。

--#--
If this is still not short enough for you, there is a next step using the
`macro` macro:
--#--
これでもまだ十分短くないと感じたのなら、`macro` を使ったさらなるステップを見てみましょう：
-/

macro l:term:10 " ⊕ " r:term:11 : term => `((!$l && $r) || ($l && !$r))

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

/-
--#--
As you can see, `macro` is quite close to `notation` already:
- it performed syntax declaration for us
- it automatically wrote a `macro_rules` style function to match on it

--#--
見ての通り、`macro` は `notation` にもうかなり近くなっています：
- 構文宣言を代行してくれます
- 自動的に `macro_rules` スタイルの関数を書いてくれます

--#--
The are of course differences as well:
- `notation` is limited to the `term` syntax category
- `notation` cannot have arbitrary macro code on the right hand side

--#--
もちろん違いもあります：
- `notation` は `term` の構文カテゴリに限定されます
- `notation` は右側に任意のマクロコードを書くことができません

## `Syntax` Quotations
--#--
### The basics
--#--
### 基本
--#--
So far we've handwaved the `` `(foo $bar) `` syntax to both create and
match on `Syntax` objects but it's time for a full explanation since
it will be essential to all non trivial things that are syntax related.

--#--
今までは `` `(foo $bar) `` という構文を使って `Syntax` オブジェクトの作成とマッチを行ってきました。構文に関わる非自明なことに本質的に必要であるため、今こそ完全な説明を行います。

--#--
First things first we call the `` `() `` syntax a `Syntax` quotation.
When we plug variables into a syntax quotation like this: `` `($x) ``
we call the `$x` part an anti-quotation. When we insert `x` like this
it is required that `x` is of type `TSyntax y` where `y` is some `Name`
of a syntax category. The Lean compiler is actually smart enough to figure
the syntax categories that are allowed in this place out. Hence you might
sometimes see errors of the form:
--#--
まず最初に、`` `() `` という構文を `Syntax` quotation と呼びます。syntax quotation の中に変数を入れると `` `($x) `` となり、この `$x` の部分を anti-quotation と呼びます。このように `x` を挿入する場合、`x` は `TSyntax y` 型であることが求められます。ここで `y` は何かしらの構文カテゴリのとある `Name` です。Lean コンパイラは賢いため、ここで使用が許可されている構文カテゴリを把握することができます。そのため、以下のようなエラーが発生することがあります：

```
application type mismatch
  x.raw
argument
  x
has type
  TSyntax `a : Type
but is expected to have type
  TSyntax `b : Type
```
--#--
If you are sure that your thing from the `a` syntax category can be
used as a `b` here you can declare a coercion of the form:
--#--
もし `a` 構文カテゴリにあるものが `b` 構文として使えると確認していれば、次のような形で強制を宣言することができます：
-/

instance : Coe (TSyntax `a) (TSyntax `b) where
  coe s := ⟨s.raw⟩

/-!
--#--
Which will allow Lean to perform the type cast automatically. If you
notice that your `a` can not be used in place of the `b` here congrats,
you just discovered a bug in your `Syntax` function. Similar to the Lean
compiler, you could also declare functions that are specific to certain
`TSyntax` variants. For example as we have seen in the syntax chapter
there exists the function:
--#--
これによって Lean は自動的に型キャストを行うことができます。もし `a` が `b` の代わりに使えないことに気づいたなら、おめでとうございます、読者は自身の `Syntax` 関数のバグを発見しました。Lean コンパイラと同様に、特定の `TSyntax` 型に特化した関数を宣言することもできます。例えば構文の章で見たように次のような関数があります：
-/
#check TSyntax.getNat -- TSyntax.getNat : TSyntax numLitKind → Nat
/-!
--#--
Which is guaranteed to not panic because we know that the `Syntax` that
the function is receiving is a numeric literal and can thus naturally
be converted to a `Nat`.

--#--
この関数が受け取る `Syntax` は数値リテラルであり、当然 `Nat` に変換できることがわかっているため、これはパニックしないことが保証されています。

--#--
If we use the antiquotation syntax in pattern matching it will, as discussed
in the syntax chapter, give us a variable `x` of type `` TSyntax y `` where
`y` is the `Name` of the syntax category that fits in the spot where we pattern matched.
If we wish to insert a literal `$x` into the `Syntax` for some reason,
for example macro creating macros, we can escape the anti quotation using: `` `($$x) ``.

--#--
パターンマッチで anti-quotation 構文を使うと、構文の章で説明したように、`` TSyntax y `` 型の変数 `x` が得られます。ここで `y` はパターンマッチに合致した構文カテゴリの `Name` です。何らかの理由で `$x` というリテラルを `Syntax` に挿入したい場合、例えばマクロを作成する場合、anti-quotation を使ってエスケープすることができます： `` `($$x) ``。

--#--
If we want to specify the syntax kind we wish `x` to be interpreted as
we can make this explicit using: `` `($x:term) `` where `term` can be
replaced with any other valid syntax category (e.g. `command`) or parser
(e.g. `ident`).

--#--
もし `x` が解釈される構文の種類を指定したい場合は、次のようにして明示的に指定することができます：`` `($x:term) ``。ここで `term` は他の有効な構文カテゴリ（例えば `command`）やパーサ（例えば `ident`）に置き換えることができます。

--#--
So far this is only a more formal explanation of the intuitive things
we've already seen in the syntax chapter and up to now in this chapter,
next we'll discuss some more advanced anti-quotations.

--#--
ここまではすでに構文の章やこの章までに見てきた直観的な内容をより形式的に説明したにすぎません。次はより高度な anti-quotation について説明しましょう。

--#--
### Advanced anti-quotations
--#--
### より高度な anti-quotation
--#--
For convenience we can also use anti-quotations in a way similar to
format strings: `` `($(mkIdent `c)) `` is the same as: `` let x := mkIdent `c; `($x) ``.

--#--
便宜上、書式文字列と同じような方法で anti-quotations を使うこともできます：`` `($(mkIdent `c)) `` は次と同じです：`` let x := mkIdent `c; `($x) ``。

--#--
Furthermore there are sometimes situations in which we are not working
with basic `Syntax` but `Syntax` wrapped in more complex datastructures,
most notably `Array (TSyntax c)` or `TSepArray c s`. Where `TSepArray c s`, is a
`Syntax` specific type, it is what we get if we pattern match on some
`Syntax` that users a separator `s` to separate things from the category `c`.
For example if we match using: `$xs,*`, `xs` will have type `TSepArray c ","`,.
With the special case of matching on no specific separator (i.e. whitespace):
`$xs*` in which we will receive an `Array (TSyntax c)`.

--#--
さらに、いくつかのシチュエーションでは、基本的な `Syntax` ではなくより複雑なデータ構造に包まれた `Syntax`、とりわけ多いのが `Array (TSyntax c)` や `TSepArray c s` などを扱います。ここで `TSepArray c s` は `Syntax` 固有の型であり、区切り文字 `s` を使って `c` というカテゴリを区切る `Syntax` をパターンマッチした場合に得られるものです。例えば、`$xs,*` を使ってマッチをした場合、`xs` は `TSepArray c ","` という型になります。区切り文字を指定せずに（つまり空白で）マッチする特殊なケース `$xs*` では `Array (TSyntax c)` となります。

--#--
If we are dealing with `xs : Array (TSyntax c)` and want to insert it into
a quotation we have two main ways to achieve this:
1. Insert it using a separator, most commonly `,`: `` `($xs,*) ``.
  This is also the way to insert a `TSepArray c ",""`
2. Insert it point blank without a separator (TODO): `` `() ``

--#--
`xs : Array (TSyntax c)` を扱い、それを quotation に挿入したい場合、主に2つの方法があります：
1. 区切り文字を使用して挿入する。最も一般的なのは `,` を使って `` `($xs,*) `` とします。これは `TSepArray c ",""` の挿入の仕方でもあります。
2. 区切り文字無しで空白を挿入する。(TODO): `` `() ``

--#--
For example:
--#--
例えば：
-/

--#--
-- syntactically cut away the first element of a tuple if possible
--#--
-- 可能な場合にタプルの最初の要素を構文的に削除する
syntax "cut_tuple " "(" term ", " term,+ ")" : term

macro_rules
  --#--
  -- cutting away one element of a pair isn't possible, it would not result in a tuple
  --#--
  -- タプルにならないため、ペアの片方の要素を削除することは不可能
  | `(cut_tuple ($x, $y)) => `(($x, $y))
  | `(cut_tuple ($x, $y, $xs,*)) => `(($y, $xs,*))

#check cut_tuple (1, 2) -- (1, 2) : Nat × Nat
#check cut_tuple (1, 2, 3) -- (2, 3) : Nat × Nat

/-!
--#--
The last thing for this section will be so called "anti-quotation splices".
There are two kinds of anti quotation splices, first the so called optional
ones. For example we might declare a syntax with an optional argument,
say our own `let` (in real projects this would most likely be a `let`
in some functional language we are writing a theory about):
--#--
本節の最後として、いわゆる「anti-quotation スプライス」を取り上げます。anti-quotation スプライスには2種類あり、まずオプショナルと呼ばれるものから説明します。例えば、オプショナルな引数を持つ構文、独自の `let` を宣言する場合を考えます（実際のプロジェクトでは、理論を記述する対象の関数型言語の `let` である可能性が高いでしょう）：
-/

syntax "mylet " ident (" : " term)? " := " term " in " term : term

/-!
--#--
There is this optional `(" : " term)?` argument involved which can let
the user define the type of the term to the left of it. With the methods
we know so far we'd have to write two `macro_rules` now, one for the case
with, one for the case without the optional argument. However the rest
of the syntactic translation works exactly the same with and without
the optional argument so what we can do using a splice here is to essentially
define both cases at once:
--#--
オプションの `(" : " term)?` 引数を指定することで、その左側にある項の型を定義することができます。これまで見てきたメソッドでは、オプションの引数がある場合と無い場合の2つの `macro_rules` を書かなければなりませんでした。しかし、その後に行う構文変換はオプションの引数があっても無くても全く同じように動作するため、ここでスプライスをつかって出来ることは、本質的には両方のケースを一度に定義することです：
-/

macro_rules
  | `(mylet $x $[: $ty]? := $val in $body) => `(let $x $[: $ty]? := $val; $body)

/-!
--#--
The `$[...]?` part is the splice here, it basically says "if this part of
the syntax isn't there, just ignore the parts on the right hand side that
involve anti quotation variables involved here". So now we can run
this syntax both with and without type ascription:
--#--
この `$[...]?` 部分がここでのスプライスであり、基本的に「もしこの構文のこの部分が無い場合、anti-quotation 変数を含む右側においてこの部分を無視すること」ということを意味します。これで、この構文を型の帰属の有無に関わらず実行できるようになりました：
-/

#eval mylet x := 5 in x - 10 -- 0, due to subtraction behaviour of `Nat`
#eval mylet x : Int := 5 in x - 10 -- -5, after all it is an `Int` now

/-!
--#--
The second and last splice might remind readers of list comprehension
as seen for example in Python. We will demonstrate it using an implementation
of `map` as a macro:
--#--
次と最後のスプライスはPythonなどで見られるリスト内包表記を想起させるかもしれません。ここでは `map` をマクロとして実装したものを使って説明します：
-/

--#--
-- run the function given at the end for each element of the list
--#--
-- リストの各要素に対して最後に渡された関数を実行する
syntax "foreach " "[" term,* "]" term : term

macro_rules
  | `(foreach [ $[$x:term],* ] $func:term) => `(let f := $func; [ $[f $x],* ])

#eval foreach [1,2,3,4] (Nat.add 2) -- [3, 4, 5, 6]

/-!
--#--
In this case the `$[...],*` part is the splice. On the match side it tries
to match the pattern we define inside of it repetitively (given the separator
we tell it to). However unlike regular separator matching it does not
give us an `Array` or `SepArray`, instead it allows us to write another
splice on the right hand side that gets evaluated for each time the
pattern we specified matched, with the specific values from the match
per iteration.
--#--
今回の場合、`$[...],*` の部分がスプライスです。マッチする側では、その中に定義したパターンに（与えた区切り文字を考慮しながら）繰り返しマッチしようとします。しかし、正規のセパレータによるマッチとは異なり、`Array` や `SepArray` を返しません。その代わりに、指定したパターンにマッチされるたびに評価される別のスプライスを右側に書くことができます。この評価は繰り返しのたびにマッチされた特定の値で行われます。
-/

/-!
--#--
## Hygiene issues and how to solve them
--#--
### 健全性の問題とその解決策
--#--
If you are familiar with macro systems in other languages like C you
probably know about so called macro hygiene issues already.
A hygiene issue is when a macro introduces an identifier that collides with an
identifier from some syntax that it is including. For example:
--#--
C言語のような他の言語のマクロシステムに慣れている人なら、いわゆるマクロの健全性についてご存じでしょう。健全性の問題とは、マクロが識別子を導入する際に、そのマクロが含む構文の識別子と衝突してしまうことです。例えば：
-/

--#--
-- Applying this macro produces a function that binds a new identifier `x`.
--#--
-- このマクロを適用すると、新しい識別子 `x` を束縛する関数が生成される。
macro "const" e:term : term => `(fun x => $e)

--#--
-- But `x` can also be defined by a user
--#--
-- しかし `x` はユーザによって別で定義されうる
def x : Nat := 42

--#--
-- Which `x` should be used by the compiler in place of `$e`?
--#--
-- コンパイラは `$e` においてどちらの `x` を使うべきか？
#eval (const x) 10 -- 42

/-
--#--
Given the fact that macros perform only syntactic translations one might
expect the above `eval` to return 10 instead of 42: after all, the resulting
syntax should be `(fun x => x) 10`. While this was of course not the intention
of the author, this is what would happen in more primitive macro systems like
the one of C. So how does Lean avoid these hygiene issues? You can read
about this in detail in the excellent [Beyond Notations](https://lmcs.episciences.org/9362/pdf)
paper which discusses the idea and implementation in Lean in detail.
We will merely give an overview of the topic, since the details are not
that interesting for practical uses. The idea described in Beyond Notations
comes down to a concept called "macro scopes". Whenever a new macro
is invoked, a new macro scope (basically a unique number) is added to
a list of all the macro scopes that are active right now. When the current
macro introduces a new identifier what is actually getting added is an
identifier of the form:
--#--
マクロが構文の変換だけを行うことを考えると、上記の `eval` は 42 ではなく 10 を返すと期待できるかもしれません：つまるところ、返される構文は `(fun x => x) 10` となるはずだからです。もちろんこれは作者の意図したことではありませんが、C言語のような原始的なマクロシステムではこのようなことが起こります。では、Lean はこのような健全性の問題をどのように回避しているのでしょうか？これについては [Beyond Notations](https://lmcs.episciences.org/9362/pdf) という優れた論文で詳しく述べられています。この論文では Lean のアイデアと実装について詳しく論じられています。実用上、詳細はそれほど興味深いものではないので、ここではトピックの概要を述べるにとどまります。Beyond Notations で説明されているアイデアは「マクロスコープ」と呼ばれる概念に集約されます。新しいマクロが呼び出されるたびに新しいマクロスコープ（基本的には一意の番号）が現在アクティブなすべてのマクロスコープのリストに追加されます。現在のマクロが新しい識別子を導入するとき、実際に追加されるのは次の形式の識別子です：

```
<actual name>._@.(<module_name>.<scopes>)*.<module_name>._hyg.<scopes>
```
--#--
For example, if the module name is `Init.Data.List.Basic`, the name is
`foo.bla`, and macros scopes are [2, 5] we get:
--#--
例えば、モジュール名が `Init.Data.List.Basic`、名前が `foo.bla`、マクロスコープが [2, 5] の場合は以下のようになります：

```
foo.bla._@.Init.Data.List.Basic._hyg.2.5
```
--#--
Since macro scopes are unique numbers the list of macro scopes appended in the end
of the name will always be unique across all macro invocations, hence macro hygiene
issues like the ones above are not possible.

--#--
マクロスコープは一意な番号であるため、名前の末尾に付加されるマクロスコープのリストはすべてのマクロの呼び出しにおいて常に一意であり、したがって上記のようなマクロの健全性の問題は起こり得ません。

--#--
If you are wondering why there is more than just the macro scopes to this
name generation, that is because we may have to combine scopes from different files/modules.
The main module being processed is always the right most one.
This situation may happen when we execute a macro generated in a file
imported in the current file.
--#--
この名前生成になぜマクロスコープ以外のものが含まれているのか不思議に思われるかもしれませんが、これは異なるファイル・モジュールからスコープを組み合わせなければならない場合があるからです。処理されるメインモジュールは常に最も右のものです。このような状況は現在のファイルにインポートされたファイルで生成されたマクロを実行する時に発生する可能性があります。

```
foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr_hyg.4
```
--#--
The delimiter `_hyg` at the end is used just to improve performance of
the function `Lean.Name.hasMacroScopes` -- the format could also work without it.

--#--
末尾の区切り文字 `_hyg` は関数 `Lean.Name.hasMacroScopes` のパフォーマンスを向上させるためだけに使用されています。つまりこのフォーマットではこの区切り文字が無くても動作はします。

--#--
This was a lot of technical details. You do not have to understand them
in order to use macros, if you want you can just keep in mind that Lean
will not allow name clashes like the one in the `const` example.

--#--
これには技術的な詳細が多く含まれていました。マクロを使うにあたってはこれらを理解する必要はありません。もし必要であれば、Lean は `const` の例のような名前の衝突を許さないということだけを覚えておいてください。

--#--
Note that this extends to *all* names that are introduced using syntax
quotations, that is if you write a macro that produces:
`` `(def foo := 1) ``, the user will not be able to access `foo`
because the name will subject to hygiene. Luckily there is a way to
circumvent this. You can use `mkIdent` to generate a raw identifier,
for example: `` `(def $(mkIdent `foo) := 1) ``. In this case it won't
be subject to hygiene and accessible to the user.

--#--
これは syntax quotation で導入される **全て** の名前に拡張されます。つまり、`` `(def foo := 1) `` を生成するマクロを書いた場合、`foo` は健全性の対象であるためユーザは `foo` にアクセスすることができません。幸い、これを回避する方法があります。例えば、`` `(def $(mkIdent `foo) := 1) `` のように `mkIdent` を使って生の識別子を生成することができます。この場合、識別子は健全性の管理から外れ、ユーザがアクセスできるようになります。

--#--
## `MonadQuotation` and `MonadRef`
--#--
## `MonadQuotation` と `MonadRef`
--#--
Based on this description of the hygiene mechanism one interesting
question pops up, how do we know what the current list of macro scopes
actually is? After all in the macro functions that were defined above
there is never any explicit passing around of the scopes happening.
As is quite common in functional programming, as soon as we start
having some additional state that we need to bookkeep (like the macro scopes)
this is done with a monad, this is the case here as well with a slight twist.

--#--
この健全性のメカニズムの説明に基づくと、1つの興味深い疑問が浮かんできます。現在のマクロスコープがどうなっているかを知る方法はあるでしょうか？結局のところ、上で定義したマクロ関数ではスコープの明示的な受け渡しは一切行われていません。関数型プログラミングではよくあることですが、（マクロスコープなどの）管理する必要のある追加状態を持ち始めると、それらはすぐにモナドで管理されます。このケースでは少々ひねられていますが、同様です。

--#--
Instead of implementing this for only a single monad `MacroM` the general
concept of keeping track of macro scopes in monadic way is abstracted
away using a type class called `MonadQuotation`. This allows any other
monad to also easily provide this hygienic `Syntax` creation mechanism
by simply implementing this type class.

--#--
これを単一のモナド `MacroM` だけに実装する代わりに、`MonadQuotation` という型クラスを使って、モナド的な方法でマクロスコープを追跡する一般的な概念を抽象化しています。これにより、他のモナドでもこの型クラスを実装するだけでこの健全な `Syntax` 作成アルゴリズムを簡単に提供できるようになります。

--#--
This is also the reason that while we are able to use pattern matching on syntax
with `` `(syntax) `` we cannot just create `Syntax` with the same
syntax in pure functions: there is no `Monad` implementing `MonadQuotation`
involved in order to keep track of the macro scopes.

--#--
これが `` `(syntax) `` で構文のパターンマッチを使用することができる一方で、純粋関数で同じ構文を持つ `Syntax` を作成することができない理由でもあります：純粋関数にはマクロスコープを追跡するための `MonadQuotation` を備えた `Monad` を持たないためです。

--#--
Now let's take a brief look at the `MonadQuotation` type class:
--#--
では、`MonadQuotation` 型クラスを簡単に見てみましょう：
-/

namespace Playground

class MonadRef (m : Type → Type) where
  getRef      : m Syntax
  withRef {α} : Syntax → m α → m α

class MonadQuotation (m : Type → Type) extends MonadRef m where
  getCurrMacroScope : m MacroScope
  getMainModule     : m Name
  withFreshMacroScope {α : Type} : m α → m α

end Playground

/-
--#--
Since `MonadQuotation` is based on `MonadRef`, let's take a look at `MonadRef`
first. The idea here is quite simple: `MonadRef` is meant to be seen as an extension
to the `Monad` typeclass which
- gives us a reference to a `Syntax` value with `getRef`
- can evaluate a certain monadic action `m α` with a new reference to a `Syntax`
  using `withRef`

--#--
`MonadQuotation` は `MonadRef` に基づいているため、まずは `MonadRef` を見てみましょう。これのアイデアは非常にシンプルです：`MonadRef` は `Monad` 型クラスを以下の観点で拡張したものです。
- `getRef` で取得される `Syntax` への参照の利用
- あるモナドアクション `m α` を `withRed` を使って `Syntax` への新しい参照で評価できる

--#--
On it's own `MonadRef` isn't exactly interesting, but once it is combined with
`MonadQuotation` it makes sense.

--#--
`MonadRef` 単体では対して面白くありませんが、`MonadQuotation` と組み合わさることで意味が生まれます。

--#--
As you can see `MonadQuotation` extends `MonadRef` and adds 3 new functions:
- `getCurrMacroScope` which obtains the latest `MacroScope` that was created
- `getMainModule` which (obviously) obtains the name of the main module,
  both of these are used to create these hygienic identifiers explained above
- `withFreshMacroScope` which will compute the next macro scope and run
  some computation `m α` that performs syntax quotation with this new
  macro scope in order to avoid name clashes. While this is mostly meant
  to be used internally whenever a new macro invocation happens, it can sometimes
  make sense to use this in our own macros, for example when we are generating
  some syntax block repeatedly and want to avoid name clashes.

--#--
見ての通り、`MonadQuotation` は `MonadRef` を拡張し、3つの新しい関数を追加しています：
- `getCurrMacroScope` は作成された中で最新の `MacroScope` を取得します。
- `getMainModule` では（明らかに）メインモジュールの名前を取得します。これは上記で説明した健全な識別子の作成にも使用されます。
- `withFreshMacroScope` は次のマクロスコープを計算し、名前の衝突を避けるためのこの新しいスコープで syntax quotation を行う計算 `m α` を実行します。これは新しいマクロの呼び出しが発生するたびに内部的に使用されることを意図していますが、例えば構文ブロックを繰り返し生成していて、名前の衝突を避けたい場合など、独自のマクロでこれを使用する意味がある場合もあります。

--#--
How `MonadRef` comes into play here is that Lean requires a way to indicate
errors at certain positions to the user. One thing that wasn't introduced
in the `Syntax` chapter is that values of type `Syntax` actually carry their
position in the file around as well. When an error is detected, it is usually
bound to a `Syntax` value which tells Lean where to indicate the error in the file.
What Lean will do when using `withFreshMacroScope` is to apply the position of
the result of `getRef` to each introduced symbol, which then results in better
error positions than not applying any position.

--#--
ここで `MonadRef` がどのように関わってくるかというと、Lean は特定の位置でのエラーをユーザに示す方法を必要としています。`Syntax` の章では紹介しませんでしたが、`Syntax` 型の値は実際にファイル内の位置も持ち運ぶことができます。エラーが検出されると、これは通常 `Syntax` 型の値に束縛され、Lean にファイルのどこでエラーが発生したかを伝えます。`withFreshMacroScope` を使って Lean は `getRef` の結果の位置を導入された各シンボルに適用し、その結果位置を適用しない場合より良いエラー位置が得られます。

--#--
To see error positioning in action, we can write a little macro that makes use of it:
--#--
エラー位置の動作を見るために、これを利用する小さなマクロを書いてみましょう：
-/

syntax "error_position" ident : term

macro_rules
  | `(error_position all) => Macro.throwError "Ahhh"
  --#--
  -- the `%$tk` syntax gives us the Syntax of the thing before the %,
  -- in this case `error_position`, giving it the name `tk`
  --#--
  -- `%$tk` 構文によって % より前の Syntax が得られる
  -- ここでは `error_position` であり、`tk` と名付けられる
  | `(error_position%$tk first) => withRef tk (Macro.throwError "Ahhh")

#check_failure error_position all -- the error is indicated at `error_position all`
#check_failure error_position first -- the error is only indicated at `error_position`

/-
--#--
Obviously controlling the positions of errors in this way is quite important
for a good user experience.

--#--
このようにエラーの位置をコントロールすることは、良いユーザエクスペリエンスにとって非常に重要であることは明らかでしょう。

--#--
## Mini project
--#--
## ミニプロジェクト
--#--
As a final mini project for this section we will re-build the arithmetic
DSL from the syntax chapter in a slightly more advanced way, using a macro
this time so we can actually fully integrate it into the Lean syntax.
--#--
この節の最後のミニプロジェクトとして、構文の章で出てきた算術 DSL を、今回はマクロを使ってもう少し高度な方法で再構築し、実際に Lean の構文に完全に統合できるようにします。
-/
declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith
syntax "[Arith|" arith "]" : term

macro_rules
  | `([Arith| $x:num]) => `($x)
  | `([Arith| $x:arith + $y:arith]) => `([Arith| $x] + [Arith| $y]) -- recursive macros are possible
  | `([Arith| $x:arith - $y:arith]) => `([Arith| $x] - [Arith| $y])
  | `([Arith| ($x:arith)]) => `([Arith| $x])

#eval [Arith| (12 + 3) - 4] -- 11

/-!
--#--
Again feel free to play around with it. If you want to build more complex
things, like expressions with variables, maybe consider building an inductive type
using macros instead. Once you got your arithmetic expression term
as an inductive, you could then write a function that takes some form of
variable assignment and evaluates the given expression for this
assignment. You could also try to embed arbitrary `term`s into your
arith language using some special syntax or whatever else comes to your mind.
--#--
ここでも自由に遊んでみてください。変数を使った式のようなより複雑なものを作りたい場合は、マクロを使う代わりに帰納型を作ることを検討してみてください。算術式の項を帰納型にした場合、何らかの形で変数に代入し、その式を評価する関数を書くことができます。また、特別な構文や思いついたものを使って、任意の `term` を算術式に埋め込んでみることもできます。
-/

/-!
--#--
## More elaborate examples
--#--
## さらなるエラボレートの例
--#--
### Binders 2.0
--#--
### 束縛子 2.0
--#--
As promised in the syntax chapter here is Binders 2.0. We'll start by
reintroducing our theory of sets:
--#--
構文の章で約束したように、パワーアップした束縛子を導入しましょう。まず集合論を再び導入することから始めます：
-/
def Set (α : Type u) := α → Prop
def Set.mem (x : α) (X : Set α) : Prop := X x

--#--
-- Integrate into the already existing typeclass for membership notation
--#--
-- すでに存在する所属の記法用の型クラスに統合
instance : Membership α (Set α) where
  mem := Set.mem

def Set.empty : Set α := λ _ => False

--#--
-- the basic "all elements such that" function for the notation
--#--
-- 「～であるようなすべての要素」という基本的な関数のための記法
def setOf {α : Type} (p : α → Prop) : Set α := p

/-!
--#--
The goal for this section will be to allow for both `{x : X | p x}`
and `{x ∈ X, p x}` notations. In principle there are two ways to do this:
1. Define a syntax and macro for each way to bind a variable we might think of
2. Define a syntax category of binders that we could reuse across other
   binder constructs such as `Σ` or `Π` as well and implement macros for
   the `{ | }` case

--#--
この節の目標は `{x : X | p x}` と `{x ∈ X, p x}` の両方の表記を可能にすることです。原理的には2つの方法があります：
1. 対象の変数を束縛する方法についての構文とマクロを定義する
2. `Σ` や `Π` などの他の束縛構文でも再利用できるような束縛の構文カテゴリを定義し、`{ | }` の場合のマクロを実装する

--#--
In this section we will use approach 2 because it is more easily reusable.
--#--
本節では、再利用が容易なアプローチ 2 を使用します。
-/

declare_syntax_cat binder_construct
syntax "{" binder_construct "|" term "}" : term

/-!
--#--
Now let's define the two binders constructs we are interested in:
--#--
さて、本題である2つの束縛子を定義してみましょう：
-/
syntax ident " : " term : binder_construct
syntax ident " ∈ " term : binder_construct

/-!
--#--
And finally the macros to expand our syntax:
--#--
そして最後に構文を拡張するためのマクロです：
-/

macro_rules
  | `({ $var:ident : $ty:term | $body:term }) => `(setOf (fun ($var : $ty) => $body))
  | `({ $var:ident ∈ $s:term | $body:term }) => `(setOf (fun $var => $var ∈ $s ∧ $body))

--#--
-- Old examples with better syntax:
--#--
-- 以前の例は改良した構文では以下のようになる：
#check { x : Nat | x ≤ 1 } -- setOf fun x => x ≤ 1 : Set Nat

example : 1 ∈ { y : Nat | y ≤ 1 } := by simp[Membership.mem, Set.mem, setOf]
example : 2 ∈ { y : Nat | y ≤ 3 ∧ 1 ≤ y } := by simp[Membership.mem, Set.mem, setOf]

--#--
-- New examples:
--#--
-- 新しい例：
def oneSet : Set Nat := λ x => x = 1
#check { x ∈ oneSet | 10 ≤ x } -- setOf fun x => x ∈ oneSet ∧ 10 ≤ x : Set Nat

example : ∀ x, ¬(x ∈ { y ∈ oneSet | y ≠ 1 }) := by
  intro x h
  -- h : x ∈ setOf fun y => y ∈ oneSet ∧ y ≠ 1
  -- ⊢ False
  cases h
  -- : x ∈ oneSet
  -- : x ≠ 1
  contradiction


/-!
--#--
## Reading further
--#--
## さらに読む
--#--
If you want to know more about macros you can read:
- the API docs: TODO link
- the source code: the lower parts of [Init.Prelude](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean)
  as you can see they are declared quite early in Lean because of their importance
  to building up syntax
- the aforementioned [Beyond Notations](https://lmcs.episciences.org/9362/pdf) paper
--#--
マクロについてさらに知りたい場合は以下を読むと良いでしょう：
- API のドキュメント：TODO link
- ソースコード：[Init.Prelude](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean) の前半部分。Lean において構文を構築するためにこれらは重要であるため、これらの宣言はファイル中のかなり初めのほうにあることがわかるでしょう。
- 前述した論文 [Beyond Notations](https://lmcs.episciences.org/9362/pdf)
-/
