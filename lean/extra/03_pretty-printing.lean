/-
--#--
# Extra: Pretty Printing
--#--
# 付録：プリティプリント
--#--
The pretty printer is what Lean uses to present terms that have been
elaborated to the user. This is done by converting the `Expr`s back into
`Syntax` and then even higher level pretty printing datastructures. This means
Lean does not actually recall the `Syntax` it used to create some `Expr`:
there has to be code that tells it how to do that.
In the big picture, the pretty printer consists of three parts run in the
order they are listed in:

--#--
プリティプリンタとは、Lean がエラボレートした項をユーザに提示するために使用されるものです。これは `Expr` を `Syntax` に変換し、さらに高レベルのプリティプリント用データ構造に戻すことで行われます。これは Lean が `Expr` を作成する際に使用した実際の `Syntax` を思い出すわけではないことを意味します：もしそうであればその方法を指示するコードがあるはずですから。全体像として、プリティプリンタは3つの部分から構成されています：

--#--
- the **[delaborator](https://github.com/leanprover/lean4/tree/master/src/Lean/PrettyPrinter/Delaborator)**
  this will be our main interest since we can easily extend it with our own code.
  Its job is to turn `Expr` back into `Syntax`.
- the **[parenthesizer](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Parenthesizer.lean)**
  responsible for adding parenthesis into the `Syntax` tree, where it thinks they would be useful
- the **[formatter](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Formatter.lean)**
  responsible for turning the parenthesized `Syntax` tree into a `Format` object that contains
  more pretty printing information like explicit whitespaces

--#--
- **[デラボレータ](https://github.com/leanprover/lean4/tree/master/src/Lean/PrettyPrinter/Delaborator)**、この部分は簡単に独自のコードで拡張ができることもあり最も興味深い部分です。このパートの仕事は `Expr` を `Syntax` に戻すことです。
- **[parenthesizer](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Parenthesizer.lean)** は `Syntax` 木に便利だと思われる位置に括弧を追加する役割を持ちます。
- **[フォーマッタ](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Formatter.lean)** は括弧が付けられた `Syntax` 木に明示的なスペースを入れるなどのよりプリティプリントな情報を含む `Format` オブジェクトに変換する役割を持ちます。

--#--
## Delaboration
--#--
## デラボレーション
--#--
As its name suggests, the delaborator is in a sense the opposite of the
elaborator. The job of the delaborator is to take an `Expr` produced by
the elaborator and turn it back into a `Syntax` which, if elaborated,
should produce an `Expr` that behaves equally to the input one.

--#--
その名前が示すように、デラボレータはある意味においてエラボレータの反対です。デラボレータの仕事は、エラボレータが生成した `Expr` を受け取り、`Syntax` に戻すことです。ここで生成される `Syntax` はエラボレートされると、デラボレータに入力された `Expr` と同じものを出力しなければなりません。

--#--
Delaborators have the type `Lean.PrettyPrinter.Delaborator.Delab`. This
is an alias for `DelabM Syntax`, where `DelabM` is the delaboration monad.
All of this machinery is defined [here](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Delaborator/Basic.lean).
`DelabM` provides us with quite a lot of options you can look up in the documentation
(TODO: Docs link). We will merely highlight the most relevant parts here.

--#--
デラボレータは `Lean.PrettyPrinter.Delaborator.Delab` という型を持ちます。これは `DelabM Syntax` のエイリアスで、`DelabM` はデラボレーションのためのモナドです。この機構についてはすべて [ここ](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Delaborator/Basic.lean) にて定義されています。`DelabM` は非常に多くのオプションを提供しており、これはドキュメントから探すことができます（TODO: Docs link）。ここでは単に最も関連性のある部分を強調します。

--#--
- It has a `MonadQuotation` instance which allows us to declare `Syntax` objects
  using the familiar quotation syntax.
- It can run `MetaM` code.
- It has a `MonadExcept` instance for throwing errors.
- It can interact with `pp` options using functions like `whenPPOption`.
- You can obtain the current subexpression using `SubExpr.getExpr`. There is
  also an entire API defined around this concept in the `SubExpr` module.

--#--
- `MonadQuotation` インスタンスを持っており、おなじみのquotation構文を使って `Syntax` オブジェクトを宣言することができます。
- `MetaM` のコードを実行することができます。
- 例外を投げるための `MonadExcept` インスタンスを持ちます。
- `whenPPOption` のような関数を使うことで `pp` オプションを操作することができます。
- 現在の部分式を取得するには `SubExpr.getExpr` を使用します。また、`SubExpr` モジュールには、この概念を扱う API 全体が定義されています。

--#--
### Making our own
--#--
### 独自のデラボレータを作る
--#--
Like so many things in metaprogramming the elaborator is based on an attribute,
in this case the `delab` one. `delab` expects a `Name` as an argument,
this name has to start with the name of an `Expr` constructor, most commonly
`const` or `app`. This constructor name is then followed by the name of the
constant we want to delaborate. For example, if we want to delaborate a function
`foo` in a special way we would use `app.foo`. Let's see this in action:
--#--
メタプログラミングの多くのものと同様に、エラボレータは属性に基づいており、今回の場合では `delab` です。`delab` は引数として `Name` を受け取り、この名前は `Expr` コンストラクタの名前で始まる必要があり、最も一般的あなのは `const` か `app` です。このコンストラクタ名の後にデラボレートしたい定数の名前が続きます。例えば、関数 `foo` を特別な方法でデラボレートしたい場合は `app.foo` を使います。これを実際にやってみましょう：
-/

import Lean

open Lean PrettyPrinter Delaborator SubExpr

def foo : Nat → Nat := fun x => 42

@[delab app.foo]
def delabFoo : Delab := do
  `(1)

#check foo -- 1 : Nat → Nat
#check foo 13 -- 1 : Nat, full applications are also pretty printed this way

/-!
--#--
This is obviously not a good delaborator since reelaborating this `Syntax`
will not yield the same `Expr`. Like with many other metaprogramming
attributes we can also overload delaborators:
--#--
この `Syntax` を再度エラボレートしても同じ `Expr` は得られないため、明らかに良いデラボレータではありません。他の多くのメタプログラミングの属性と同様に、デラボレータをオーバーロードすることもできます：
-/

@[delab app.foo]
def delabfoo2 : Delab := do
  `(2)

#check foo -- 2 : Nat → Nat

/-!
--#--
The mechanism for figuring out which one to use is the same as well. The
delaborators are tried in order, in reverse order of registering, until one
does not throw an error, indicating that it "feels unresponsible for the `Expr`".
In the case of delaborators, this is done using `failure`:
--#--
それを使うかを判断するメカニズムも同じです。デラボレータは登録された順番の逆順に、「`Expr` に対して責任が無いと感じる」ことを示すエラーを投げないものまで試行されます。デラボレータの場合、これは `failure` を使って行われます：
-/

@[delab app.foo]
def delabfoo3 : Delab := do
  failure
  `(3)

#check foo -- 2 : Nat → Nat, still 2 since 3 failed

/-!
--#--
In order to write a proper delaborator for `foo`, we will have to use some
slightly more advanced machinery though:
--#--
`foo` のための適切なデラボレータを書くためにはもう少し高度な機構を使う必要があります：
-/

@[delab app.foo]
def delabfooFinal : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' `foo 1 -- only delab full applications this way
  let fn := mkIdent `fooSpecial
  let arg ← withAppArg delab
  `($fn $arg)

#check foo 42 -- fooSpecial 42 : Nat
#check foo -- 2 : Nat → Nat, still 2 since 3 failed

/-!
--#--
Can you extend `delabFooFinal` to also account for non full applications?

--#--
読者は `delabFooFinal` を拡張して、完全でない適用も考慮することができるでしょうか？

## Unexpanders
--#--
While delaborators are obviously quite powerful it is quite often not necessary
to use them. If you look in the Lean compiler for `@[delab` or rather `@[builtin_delab`
(a special version of the `delab` attribute for compiler use, we don't care about it),
you will see there are quite few occurrences of it. This is because the majority
of pretty printing is in fact done by so called unexpanders. Unlike delaborators
they are of type `Lean.PrettyPrinter.Unexpander` which in turn is an alias for
`Syntax → Lean.PrettyPrinter.UnexpandM Syntax`. As you can see, they are
`Syntax` to `Syntax` translations, quite similar to macros, except that they
are supposed to be the inverse of macros. The `UnexpandM` monad is quite a lot
weaker than `DelabM` but it still has:

--#--
デラボレータは明らかに強力ですが、使う必要がないことも良くあります。Lean コンパイラにて `@[delab` か `@[builtin_delab`（コンパイラ用の特別バージョンの `delab` 属性）を探してみるとほとんど出てこないことがわかるでしょう。というのも、プリティプリントの大部分はいわゆる unexpander によって行われるからです。デラボレータとは異なり、これらは `Lean.PrettyPrinter.Unexpander` 型で、これは `Syntax → Lean.PrettyPrinter.UnexpandM Syntax` のエイリアスです。見ての通り、これらは `Syntax` から `Syntax` への変換で、マクロの逆であることを除けばマクロによく似ています。`UnexpandM` モナドは `DelabM` よりもかなり弱いですが、それでも下記の機能を持ちます：

--#--
- `MonadQuotation` for syntax quotations
- The ability to throw errors, although not very informative ones: `throw ()`
  is the only valid one

--#--
- syntax quotation のための `MonadQuotation`
- 例外の送出機能、ただこれはあまり有益なものではありません：唯一有効なのは `throw ()` だけです。

--#--
Unexpanders are always specific to applications of one constant. They are registered
using the `app_unexpander` attribute, followed by the name of said constant. The unexpander
is passed the entire application of the constant after the `Expr` has been delaborated,
without implicit arguments. Let's see this in action:
--#--
unexpander は常にある1つの定数の適用に対して固有です。これらは `app_unexpander` 属性と、それに続く対象の定数名を使って登録されます。unexpander には暗黙の引数無しで `Expr` がデラボレートされた後に、定数の適用全体が渡されます。これを実際に見てみましょう：
-/

def myid {α : Type} (x : α) := x

@[app_unexpander myid]
def unexpMyId : Unexpander
  --#--
  -- hygiene disabled so we can actually return `id` without macro scopes etc.
  --#--
  -- 健全性を無効にすることで、マクロスコープなどを使わずに `id` を実際に返すことができる。
  | `(myid $arg) => set_option hygiene false in `(id $arg)
  | `(myid) => pure $ mkIdent `id
  | _ => throw ()

#check myid 12 -- id 12 : Nat
#check myid -- id : ?m.3870 → ?m.3870

/-!
--#--
For a few nice examples of unexpanders you can take a look at
[NotationExtra](https://github.com/leanprover/lean4/blob/master/src/Init/NotationExtra.lean)

--#--
unexpander についていくつかの良例は [NotationExtra](https://github.com/leanprover/lean4/blob/master/src/Init/NotationExtra.lean) を参照してください。

--#--
### Mini project
--#--
### ミニプロジェクト
--#--
As per usual, we will tackle a little mini project at the end of the chapter.
This time we build our own unexpander for a mini programming language.
Note that many ways to define syntax already have generation of the required
pretty printer code built-in, e.g. `infix`, and `notation` (however not `macro_rules`).
So, for easy syntax, you will never have to do this yourself.
--#--
いつものように、章の最後にてちょっとしたミニプロジェクトに取り組んでみます。今回はミニプログラミング言語のための独自の unexpander を作ります。`infix` や `notation` のような構文を定義するための多くの方法には必要なプリティプリンタコードを生成する機能がすでに組み込まれていることに注意してください（ただし、`macro_rules` には含まれていません）。そのため、簡単な構文であれば、自分でこれを行う必要はないでしょう。
-/

declare_syntax_cat lang
syntax num   : lang
syntax ident : lang
syntax "let " ident " := " lang " in " lang: lang
syntax "[Lang| " lang "]" : term

inductive LangExpr
  | numConst : Nat → LangExpr
  | ident    : String → LangExpr
  | letE     : String → LangExpr → LangExpr → LangExpr

macro_rules
  | `([Lang| $x:num ]) => `(LangExpr.numConst $x)
  | `([Lang| $x:ident]) => `(LangExpr.ident $(Lean.quote (toString x.getId)))
  | `([Lang| let $x:ident := $v:lang in $b:lang]) => `(LangExpr.letE $(Lean.quote (toString x.getId)) [Lang| $v] [Lang| $b])

instance : Coe NumLit (TSyntax `lang) where
  coe s := ⟨s.raw⟩

instance : Coe Ident (TSyntax `lang) where
  coe s := ⟨s.raw⟩

-- LangExpr.letE "foo" (LangExpr.numConst 12)
--   (LangExpr.letE "bar" (LangExpr.ident "foo") (LangExpr.ident "foo")) : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]

/-!
--#--
As you can see, the pretty printing output right now is rather ugly to look at.
We can do better with an unexpander:
--#--
見ての通り、現時点の表示される出力はかなり醜いものになっています。unexpander を使えばもっとよくなります：
-/

@[app_unexpander LangExpr.numConst]
def unexpandNumConst : Unexpander
  | `(LangExpr.numConst $x:num) => `([Lang| $x])
  | _ => throw ()

@[app_unexpander LangExpr.ident]
def unexpandIdent : Unexpander
  | `(LangExpr.ident $x:str) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| $name])
  | _ => throw ()

@[app_unexpander LangExpr.letE]
def unexpandLet : Unexpander
  | `(LangExpr.letE $x:str [Lang| $v:lang] [Lang| $b:lang]) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| let $name := $v in $b])
  | _ => throw ()

-- [Lang| let foo := 12 in foo] : LangExpr
#check [Lang|
  let foo := 12 in foo
]

-- [Lang| let foo := 12 in let bar := foo in foo] : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]

/-!
--#--
That's much better! As always, we encourage you to extend the language yourself
with things like parenthesized expressions, more data values, quotations for
`term` or whatever else comes to your mind.
--#--
この方がずっと良いです！いつものように読者は、括弧でくくられた式や、より多くのデータ値、`term` の引用など思いついたものを使って自分で言語を拡張することをお勧めします。
-/
