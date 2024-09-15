/-
--#--
# Introduction

--#--
# はじめに

--#--
## What's the goal of this book?

--#--
## 本書のゴール

--#--
This book aims to build up enough knowledge about metaprogramming in Lean 4 so
you can be comfortable enough to:

--#--
本書はLean4におけるメタプログラミングについて十分な知識を得ることを目的にしています：

--#--
* Start building your own meta helpers (defining new Lean notation such as `∑`,
building new Lean commands such as `#check`, writing tactics such as `use`, etc.)
* Read and discuss metaprogramming APIs like the ones in Lean 4 core and
Mathlib4

--#--
* 読者独自によるメタヘルパーを作るところから始めます（`∑` のような新しいLeanの記法の定義や、`#check` のような新しいLeanコマンドの作成、`use` のようなタクティクの記述など）。
* Lean4のコアやMathlib4にあるようなメタプログラミングAPIを読み、議論します。

--#--
We by no means intend to provide an exhaustive exploration/explanation of the
entire Lean 4 metaprogramming API. We also don't cover the topic of monadic
programming in Lean 4. However, we hope that the examples provided will be
simple enough for the reader to follow and comprehend without a super deep
understanding of monadic programming. The book
[Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/)
is a highly recommended source on that subject.

--#--
決してLean4のメタプログラミングAPI全体を網羅的に説明するつもりはありません。また、Lean4のモナドによるプログラミングについての話題も扱いません。しかし、本書で提供する例が十分にシンプルであり、モナドプログラミングについての超深い理解がなくとも読者がフォローして理解できることを望みます。このテーマについては [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/) という本がお勧めです。 [^fn1]

--#--
## Book structure

--#--
## 本書の構成

--#--
The book is organized in a way to build up enough context for the chapters that
cover DSLs and tactics. Backtracking the pre-requisites for each chapter, the
dependency structure is as follows:

--#--
本書はDSLとタクティクを扱う章に十分な文脈を構築できるように構成されています。各章の前提条件を遡ると、依存関係は以下のような構造になっています：

--#--
* "Tactics" builds on top of "Macros" and "Elaboration"
* "DSLs" builds on top of "Elaboration"
* "Macros" builds on top of "`Syntax`"
* "Elaboration" builds on top of "`Syntax`" and "`MetaM`"
* "`MetaM`" builds on top of "Expressions"

--#--
* 「タクティク」は「マクロ」と「エラボレーション」上に構築されます。
* 「DSL」は「エラボレーション」上に構築されます。
* 「マクロ」は「`Syntax`」上に構築されます。
* 「エラボレーション」は「`Syntax`」と「`MetaM`」上に構築されます。
* 「`MetaM`」は「式」上に構築されます。

--#--
After the chapter on tactics, you find a cheat sheet containing a wrap-up of key
concepts and functions. And after that, there are some chapters with extra
content, showing other applications of metaprogramming in Lean 4. Most chapters contain exercises at the end of the chapter - and at the end of the book you will have full solutions to those exercises.

--#--
タクティクの章の後には、重要な概念と帰納の総括を含むチートシートがありまず。そしてその後には付録としてLean4のメタプログラミングの応用例の章を用意しています。ほとのどの章の章末に演習問題があり、本の最後にはそれらの解答が載っています。

--#--
The rest of this chapter is a gentle introduction to what metaprogramming is,
offering some small examples to serve as appetizers for what the book shall
cover.

--#--
本章の残りはメタプログラミングとは何かについてやさしく紹介し、本書で扱う内容の前菜となるような小さな例をいくつか提供します。

--#--
Note: the code snippets aren't self-contained. They are supposed to be run/read
incrementally, starting from the beginning of each chapter.

--#--
注意：それぞれのコード片は自己完結していません。各章の初めから少しずつ実行/読むことを想定しています。

--#--
## What does it mean to be in meta?

--#--
## メタとはどういう意味か？

--#--
When we write code in most programming languages such as Python, C, Java or
Scala, we usually have to stick to a pre-defined syntax otherwise the compiler
or the interpreter won't be able to figure out what we're trying to say. In
Lean, that would be defining an inductive type, implementing a function, proving
a theorem, etc. The compiler, then, has to parse the code, build an AST (abstract
syntax tree) and elaborate its syntax nodes into terms that can be processed by
the language kernel. We say that such activities performed by the compiler are
done in the __meta-level__, which will be studied throughout the book. And we
also say that the common usage of the language syntax is done in the
__object-level__.

--#--
Python・C・Java・Scalaなどほとんどのプログラミング言語でコードを書くとき、通常はあらかじめ定義された構文に従わなければなりません。そうしなければコンパイラやインタプリタは我々の言わんとしていることを理解できないでしょう。Leanにおいては帰納型の定義、関数の実装、定理の証明などがこれにあたります。これを受けてコンパイラはコードをパースし、AST（抽象構文木）を構築し、その構文ノードを言語カーネルが処理できる項に精緻化しなければなりません。このようなコンパイラが行う活動は **メタレベル** で行われると表現され、これが本書を通じて学んでいくものです。また、言語構文の一般的な使用は **オブジェクトレベル** で行われると言います。

--#--
In most systems, the meta-level activities are done in a different language to
the one that we use to write code. In Isabelle, the meta-level language is ML
and Scala. In Coq, it's OCaml. In Agda, it's Haskell. In Lean 4, the meta code is
mostly written in Lean itself, with a few components written in C++.

--#--
ほとんどのシステムでは、メタレベルの活動はコードの記述で使う言語とは別の言語で行われます。Isabelleでは、メタレベル言語はMLとScalaです。CoqではOcamlです。AgdaではHaskellです。Lean4では、C++で書かれたいくつかのコンポーネント以外、メタコードのほとんどはLean自身で記述されます。

--#--
One cool thing about Lean, though, is that it allows us to define custom syntax
nodes and implement meta-level routines to elaborate them in the
very same development environment that we use to perform object-level
activities. So for example, one can write notation to instantiate a
term of a certain type and use it right away, in the same file! This concept is
generally called
[__reflection__](https://en.wikipedia.org/wiki/Reflective_programming). We can
say that, in Lean, the meta-level is _reflected_ to the object-level.

--#--
しかし、Leanのステキな点は、オブジェクトレベルで活動するのとまったく同じ開発環境でカスタム構文ノードを定義し、それを精緻化するメタレベルのルーチンを実装できることです。例えば、ある型の項をインスタンス化し、同じファイル内ですぐに使用するための記法を書くことができます！この概念は一般的に [リフレクション](https://ja.wikipedia.org/wiki/%E3%83%AA%E3%83%95%E3%83%AC%E3%82%AF%E3%82%B7%E3%83%A7%E3%83%B3_(%E6%83%85%E5%A0%B1%E5%B7%A5%E5%AD%A6)) と呼ばれています。それゆえLeanでは、メタレベルはオブジェクトレベルに **リフレクション** されると言うことができます。

--#--
If you have done some metaprogramming in languages such as Ruby, Python or Javascript,
it probably took the form of making use of predefined metaprogramming methods to define
something on the fly. For example, in Ruby you can use `Class.new` and `define_method`
to define a new class and its new method (with new code inside!) on the fly, as your program is executing.

--#--
RubyやPython、Javascriptなどの言語でメタプログラミングをしたことがある人は、おそらく定義済みのメタプログラミング用のメソッドを利用してその場で何かを定義するという形をとったことがあるでしょう。例えば、Rubyでは `Class.new` と `define_method` を使ってプログラムの実行中に新しいクラスと新しいメソッドを定義することができます。

--#--
We don't usually need to define new commands or tactics "on the fly" in Lean, but spiritually
similar feats are possible with Lean metaprogramming and are equally straightforward, e.g. you can define
a new Lean command using a simple one-liner `elab "#help" : command => do ...normal Lean code...`.

--#--
Leanでは通常、新しいコマンドやタクティクを「その場で」定義する必要はありませんが、Leanのメタプログラミングでも理屈上似たようなことが可能であり、同様に簡単に利用できます。例えば、シンプルなワンライナー `elab "#help" : command => do ...normal Lean code...` を使って新しいLeanのコマンドを定義できます。

--#--
In Lean, however, we will frequently want to directly manipulate
Lean's CST (Concrete Syntax Tree, Lean's `Syntax` type) and
Lean's AST (Abstract Syntax Tree, Lean's `Expr` type) instead of using "normal Lean code",
especially when we're writing tactics. So Lean metaprogramming is more challenging to master -
a large chunk of this book is contributed to studying these types and how we can manipulate them.

--#--
しかし、Leanでは特にタクティクを書く場合などでは、「通常のLeanコード」を使うのではなく、LeanのCST（解析木、Leanでは `Syntax` 型）やAST（抽象構文木、Leanでは `Expr` 型）を直接操作したいと思うことがよくあります。したがって、Leanのメタプログラミングをマスターすることはより難しいものになります。本書の大部分はこれらの型とその操作方法を学ぶことに費やされます。

--#--
## Metaprogramming examples

--#--
## メタプログラミングの例

--#--
Next, we introduce several examples of Lean metaprogramming, so that you start getting a taste for
what metaprogramming in Lean is, and what it will enable you to achieve. These examples are meant as
mere illustrations - do not worry if you don't understand the details for now.

--#--
ここで、Leanのメタプログラミングの例をいくつか紹介し、Leanにおけるメタプログラミングがどのようなものであり、それによって何が達成できるかを味わってもらいます。これらの例は単なる説明のためのものであり、今のところは詳細が理解できなくても心配しないでください。

--#--
### Introducing notation (defining new syntax)

--#--
### 記法の導入（新しい構文の定義）

--#--
Often one wants to introduce new notation, for example one more suitable for (a branch of) mathematics. For instance, in mathematics one would write the function adding `2` to a natural number as `x : Nat ↦ x + 2` or simply `x ↦ x + 2` if the domain can be inferred to be the natural numbers. The corresponding lean definitions `fun x : Nat => x + 2` and `fun x => x + 2` use `=>` which in mathematics means _implication_, so may be confusing to some.

--#--
例えば数学（の一分野）に適した新しい記法を導入したい場合がよくあります。例えば、数学では自然数に `2` を加える関数を `x : Nat ↦ x + 2` と書いたり、定義域が自然数であると推測できる場合は単に `x ↦ x + 2` と書いたりします。これに対応するLeanの定義 `fun x : Nat => x + 2` と `fun x => x + 2` は `=>` を使っていますが、これは数学では **含意** を意味するので、混乱する人もいるかもしれません。

--#--
We can introduce notation using a `macro` which transforms our syntax to Lean's syntax (or syntax we previously defined). Here we introduce the `↦` notation for functions.
--#--
`macro` を使って記法を導入し、Leanの構文（またはそれ以前に定義した構文）に変換することができます。ここでは、関数の `↦` 記法を導入します。
-/
import Lean

macro x:ident ":" t:term " ↦ " y:term : term => do
  `(fun $x : $t => $y)

#eval (x : Nat ↦ x + 2) 2 -- 4

macro x:ident " ↦ " y:term : term => do
  `(fun $x  => $y)

#eval (x ↦  x + 2) 2 -- 4
/-!

--#--
### Building a command

--#--
### コマンドの構築

--#--
Suppose we want to build a helper command `#assertType` which tells whether a
given term is of a certain type. The usage will be:

--#--
与えられた項が特定の型であるかどうかを示すヘルパーコマンド `#assertType` を作りたいとします。これの使い方は次のようになります：

`#assertType <term> : <type>`

--#--
Let's see the code:
--#--
このコードを見てみましょう：
-/
elab "#assertType " termStx:term " : " typeStx:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM
    try
      let tp ← elabType typeStx
      discard $ elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo "success"
    catch | _ => throwError "failure"

/-- info: success -/
#guard_msgs in --#
#assertType 5  : Nat

/-- error: failure -/
#guard_msgs in --#
#assertType [] : Nat

/-!
--#--
We started by using `elab` to define a `command` syntax. When parsed
by the compiler, it will trigger the incoming computation.

--#--
まず `elab` を使って `command` 構文を定義しました。コンパイラによってパースされると、計算が開始します。

--#--
At this point, the code should be running in the `CommandElabM` monad. We then
use `liftTermElabM` to access the `TermElabM` monad, which allows us to use
`elabType` and `elabTermEnsuringType` to build expressions out of the
syntax nodes `typeStx` and `termStx`.

--#--
この時点で、コードは `CommandElabM` モナド中で実行されるはずです。ここで `TermElabM` モナドにアクセスするために `liftTermElabM` を使用します。`TermElabM` モナドでは、`elabType` と `elabTermEnsuringType` を使って構文ノード `typeStx` と `termStx` から式を組み立てることができます。

--#--
First, we elaborate the expected type `tp : Expr`, then we use it to elaborate
the term expression. The term should have the type `tp` otherwise an error will be
thrown. We then discard the resulting term expression, since it doesn't matter to us here - we're calling
`elabTermEnsuringType` as a sanity check.

--#--
まず、期待される型 `tp : Expr` を精緻化し、次にそれを使って項の式を作成します。この項は `tp` 型でなければならず、それ以外では例外が投げられます。次に、ここでは問題にならないため結果の項の式を捨てています。なぜなら `elabTermEnsuringType` はサニティチェックとして呼ばれているからです。

--#--
We also add `synthesizeSyntheticMVarsNoPostponing`, which forces Lean to
elaborate metavariables right away. Without that line, `#assertType [] : ?_`
would result in `success`.

--#--
ここでLeanにメタ変数を精緻化するよう強制する `synthesizeSyntheticMVarsNoPostponing` も追加しています。この行がなければ、`#assertType [] : ?_` は `succsess` となってしまいます。

--#--
If no error is thrown until now then the elaboration succeeded and we can use
`logInfo` to output "success". If, instead, some error is caught, then we use
`throwError` with the appropriate message.

--#--
例外が投げられなければ、精緻化は成功したことになり、`logInfo` を使って「success」と出力することができます。もしその代わりに何らかのエラーが発生した場合、適切なメッセージを添えて `throwError` を使用します。

--#--
### Building a DSL and a syntax for it

--#--
### DSLとそのための構文の構築

--#--
Let's parse a classic grammar, the grammar of arithmetic expressions with
addition, multiplication, naturals, and variables.  We'll define an AST
(Abstract Syntax Tree) to encode the data of our expressions, and use operators
`+` and `*` to denote building an arithmetic AST. Here's the AST that we will be
parsing:
--#--
古典的な文法、つまり加算、乗算、自然数、変数を含む算術式の文法をパースしてみましょう。式のデータをエンコードするためにAST（抽象構文木）を定義し、演算子 `+` と `*` を使って算術ASTを構築します。これがこれから解析するASTです：
-/

inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | nat : Nat → Arith           -- constant
  | var : String → Arith        -- variable

/-!
--#--
Now we declare a syntax category to describe the grammar that we will be
parsing. Notice that we control the precedence of `+` and `*` by giving a lower
precedence weight to the `+` syntax than to the `*` syntax indicating that
multiplication binds tighter than addition (the higher the number, the tighter
the binding). This allows us to declare _precedence_ when defining new syntax.
--#--
ここで、構文解析を行う文法を記述するために構文カテゴリを宣言します。ここで `+` と `*` の優先順位をコントロールするために、`*` 構文よりも `+` 構文に低い優先順位の重みを与えることで、乗算は加算よりも強く束縛する（数字が大きいほど束縛が強くなる）ことを示していることに注意してください。これにより、新しい構文を定義する際に **優先順位** を宣言することができます。
-/

declare_syntax_cat arith
syntax num                        : arith -- nat for Arith.nat
syntax str                        : arith -- strings for Arith.var
syntax:50 arith:50 " + " arith:51 : arith -- Arith.add
syntax:60 arith:60 " * " arith:61 : arith -- Arith.mul
syntax " ( " arith " ) "          : arith -- bracketed expressions

--# Auxiliary notation for translating `arith` into `term`
-- `arith` を `term` に変換するための補助記法
syntax " ⟪ " arith " ⟫ " : term

--# Our macro rules perform the "obvious" translation:
-- このマクロルールは「明白な」翻訳を行う
macro_rules
  | `(⟪ $s:str ⟫)              => `(Arith.var $s)
  | `(⟪ $num:num ⟫)            => `(Arith.nat $num)
  | `(⟪ $x:arith + $y:arith ⟫) => `(Arith.add ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ $x:arith * $y:arith ⟫) => `(Arith.mul ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ ( $x ) ⟫)              => `( ⟪ $x ⟫ )

#check ⟪ "x" * "y" ⟫
-- Arith.mul (Arith.var "x") (Arith.var "y") : Arith

#check ⟪ "x" + "y" ⟫
-- Arith.add (Arith.var "x") (Arith.var "y") : Arith

#check ⟪ "x" + 20 ⟫
-- Arith.add (Arith.var "x") (Arith.nat 20) : Arith

#check ⟪ "x" + "y" * "z" ⟫ -- precedence
-- Arith.add (Arith.var "x") (Arith.mul (Arith.var "y") (Arith.var "z")) : Arith

#check ⟪ "x" * "y" + "z" ⟫ -- precedence
-- Arith.add (Arith.mul (Arith.var "x") (Arith.var "y")) (Arith.var "z") : Arith

#check ⟪ ("x" + "y") * "z" ⟫ -- brackets
-- Arith.mul (Arith.add (Arith.var "x") (Arith.var "y")) (Arith.var "z")

/-!
--#--
### Writing our own tactic

--#--
### 自前のタクティクの記述

--#--
Let's create a tactic that adds a new hypothesis to the context with a given
name and postpones the need for its proof to the very end. It's similar to
the `suffices` tactic from Lean 3, except that we want to make sure that the new
goal goes to the bottom of the goal list.

--#--
与えられた名前のコンテキストに新しい仮定を追加し、その証明の必要性を最後まで先送りするタクティクを作ってみましょう。Lean3の `suffices` タクティクと似ていますが、新しいゴールがゴールリストの一番下に来るようにした点が異なります。

--#--
It's going to be called `suppose` and is used like this:

--#--
これは `suppose` と呼ばれ、次のように使われます：

`suppose <name> : <type>`

--#--
So let's see the code:
--#--
それではコードを見てみましょう：
-/

open Lean Meta Elab Tactic Term in
elab "suppose " n:ident " : " t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  mvarId.withContext do
    let t ← elabType t
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert n t p
    replaceMainGoal [p.mvarId!, mvarIdNew]
  evalTactic $ ← `(tactic|rotate_left)

example : 0 + a = a := by
  suppose add_comm : 0 + a = a + 0
  rw [add_comm]; rfl     -- closes the initial main goal
  rw [Nat.zero_add]; rfl -- proves `add_comm`

/-!
--#--
We start by storing the main goal in `mvarId` and using it as a parameter of
`withMVarContext` to make sure that our elaborations will work with types that
depend on other variables in the context.

--#--
まずメインゴールを `mvarId` に格納し、それを `withMVarContext` のパラメータとして使用することで、コンテキスト内の他の変数に依存する型でもエラボレーションが機能するようにしています。

--#--
This time we're using `mkFreshExprMVar` to create a metavariable expression for
the proof of `t`, which we can introduce to the context using `intro1P` and
`assert`.

--#--
今回は `mkFreshExprMVar` を使って `t` の証明のためのメタ変数式を作成し、それを `intro1P` と `assert` を使ってコンテキストに導入しています。

--#--
To require the proof of the new hypothesis as a goal, we call `replaceMainGoal`
passing a list with `p.mvarId!` in the head. And then we can use the
`rotate_left` tactic to move the recently added top goal to the bottom.
--#--
新しい仮定の証明をゴールとして要求するために、`p.mvarId!` を先頭に持つリストを渡して `replaceMainGoal` を呼び出します。そして `rotate_left` タクティクを使って最近追加された一番上のゴールを一番下に移動させます。

[^fn1]: 日本語訳は https://lean-ja.github.io/fp-lean-ja/
--#--
-/
