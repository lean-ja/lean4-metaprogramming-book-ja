/-
--#--
# Syntax

--#--
# 構文

--#--
This chapter is concerned with the means to declare and operate on syntax
in Lean. Since there are a multitude of ways to operate on it, we will
not go into great detail about this yet and postpone quite a bit of this to
later chapters.

--#--
この章では、Leanにおける構文の宣言とその操作方法について説明します。構文を操作する方法はたくさんあるため、この章ではまだ詳細にあまり深入りせず、ほとんどを後の章に先送りします。

--#--
## Declaring Syntax

--#--
## 構文の宣言

--#--
### Declaration helpers

--#--
### 宣言のためのヘルパー

--#--
Some readers might be familiar with the `infix` or even the `notation`
commands, for those that are not here is a brief recap:
--#--
読者の中には `infix` や `notation` コマンドまでもご存じの方もいるかもしれませんが、そうでない方のために簡単におさらいしておきましょう：
-/

import Lean

-- XOR, denoted \oplus
infixl:60 " ⊕ " => fun l r => (!l && r) || (l && !r)

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

-- with `notation`, "left XOR"
notation:10 l:10 " LXOR " r:11 => (!l && r)

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/-
--#--
As we can see the `infixl` command allows us to declare a notation for
a binary operation that is infix, meaning that the operator is in between
the operands (as opposed to e.g. before which would be done using the `prefix` command).
The `l` at the end of `infixl` means that the notation is left associative so `a ⊕ b ⊕ c`
gets parsed as `(a ⊕ b) ⊕ c` as opposed to `a ⊕ (b ⊕ c)` (which would be achieved by `infixr`).
On the right hand side, it expects a function that operates on these two parameters
and returns some value. The `notation` command, on the other hand, allows us some more
freedom: we can just "mention" the parameters right in the syntax definition
and operate on them on the right hand side. It gets even better though, we can
in theory create syntax with 0 up to as many parameters as we wish using the
`notation` command, it is hence also often referred to as "mixfix" notation.

--#--
見てわかるように、`infixl` コマンドによって二項演算の記法を宣言することができます。この二項演算は中置（infix）、つまり演算子がオペランドの間にあることを意味します（これに対して例えば `prefix` コマンドでは意味が異なります）。`infxl` の末尾の `l` は、この記法が左結合であることを意味しており、つまり `a ⊕ b ⊕ c` は `a ⊕ (b ⊕ c)` ではなく（これは `infixr` で実現されます）、`(a ⊕ b) ⊕ c` とパースされます。このコマンドの右側では、これら2つのパラメータを操作して何らかの値を返す関数を期待しています。一方で、`notation` コマンドではより自由度が増します：構文定義の中でパラメータをただ「言及」するだけで、右側でそれを操作することができます。これにとどまらず、`notation` コマンドを使えば、理論的には0から任意の数のパラメータを指定した構文を作ることができます。このためこのコマンドはしばしば「mixfix」記法と呼ばれます。

--#--
The two unintuitive parts about these two are:
- The fact that we are leaving spaces around our operators: " ⊕ ", " LXOR ".
  This is so that, when Lean pretty prints our syntax later on, it also
  uses spaces around the operators, otherwise the syntax would just be presented
  as `l⊕r` as opposed to `l ⊕ r`.
- The `60` and `10` right after the respective commands -- these denote the operator
  precedence, meaning how strong they bind to their arguments, let's see this in action:
--#--
この2つについて直観的でない部分が2つあります：
- 演算子の周りに空白を空けていること：「 ⊕ 」、「 LXOR 」。こうすることで、Lean がこれらの構文を後から整形表示する際に、演算子の周りにもスペースを使うようになります。そうしないと構文は `l ⊕ r` ではなく `l⊕r` と表示されてしまいます。
- `60` や `10` などのそれぞれのコマンドの直後にある値は、演算子の優先順位、つまり引数との結合の強さを示しています。このことについて実際の挙動を見てみましょう：
-/

#eval true ⊕ false LXOR false -- false
#eval (true ⊕ false) LXOR false -- false
#eval true ⊕ (false LXOR false) -- true

/-!
--#--
As we can see, the Lean interpreter analyzed the first term without parentheses
like the second instead of the third one. This is because the `⊕` notation
has higher precedence than `LXOR` (`60 > 10` after all) and is thus evaluated before it.
This is also how you might implement rules like `*` being evaluated before `+`.

--#--
見てわかるように、Lean のインタプリタは括弧のない最初の項を3つ目の項ではなく2つ目の項と同じようにパースしています。これは `⊕` 記法が `LXOR` より優先順位が高いため（つまるところ `60 > 10` であるため）、`LXOR` より先に評価されます。これは `*` が `+` の前に評価されるようなルールを実装する方法でもあります。

--#--
Lastly at the `notation` example there are also these `:precedence` bindings
at the arguments: `l:10` and `r:11`. This conveys that the left argument must have
precedence at least 10 or greater, and the right argument must have precedence at 11
or greater. The way the arguments are assigned their respective precedence is by looking at
the precedence of the rule that was used to parse them. Consider for example
`a LXOR b LXOR c`. Theoretically speaking this could be parsed in two ways:
--#--
最後に、この `notation` の例では、引数に `:precedence` バインディングがあります：すなわち `l:10` と `r:11` です。これは左の引数の優先順位が少なくとも 10 以上、右の引数の優先順位が少なくとも 11 以上でなければならないことを意味しています。引数にそれぞれの優先順位を割り当てるには、その引数自体をパースするために使われたルールの優先順位を見ることで行われます。例えば `a LXOR b LXOR c` を考えてみましょう。理論的にはこれは2つのパースの仕方があります：
1. `(a LXOR b) LXOR c`
2. `a LXOR (b LXOR c)`

--#--
Since the arguments in parentheses are parsed by the `LXOR` rule with precedence
10 they will appear as arguments with precedence 10 to the outer `LXOR` rule:
--#--
括弧内の引数は優先順位 10 の `LXOR` ルールによってパースされるため、これらはその外側の `LXOR` ルールにとっては優先順位 10 の引数として表示されます：

1. `(a LXOR b):10 LXOR c`
2. `a LXOR (b LXOR c):10`

--#--
However if we check the definition of `LXOR`: `notation:10 l:10 " LXOR " r:11`
we can see that the right hand side argument requires a precedence of at least 11
or greater, thus the second parse is invalid and we remain with: `(a LXOR b) LXOR c`
assuming that:
- `a` has precedence 10 or higher
- `b` has precedence 11 or higher
- `c` has precedence 11 or higher

--#--
しかし、`LXOR`：`notation:10 l:10 " LXOR " r:11` の定義をチェックしてみると、右側の引数には少なくとも 11 以上の優先順位が必要であるため、2つ目のパースは不正であり、パース結果は `(a LXOR b) LXOR c` となり以下が仮定されます：
- `a` は 10 以上の優先順位を持つ
- `b` は 11 以上の優先順位を持つ
- `c` は 11 以上の優先順位を持つ

--#--
Thus `LXOR` is a left associative notation. Can you make it right associative?

--#--
従って、`LXOR` は左結合な記法です。読者はこれを右結合にできますか？

--#--
NOTE: If parameters of a notation are not explicitly given a precedence they will implicitly be tagged with precedence 0.

--#--
注意：ある記法のパラメータに明示的な優先順位が与えられていない場合、それらは暗黙的に優先順位 0 とタグ付けされます。

--#--
As a last remark for this section: Lean will always attempt to obtain the longest
matching parse possible, this has three important implications.
First a very intuitive one, if we have a right associative operator `^`
and Lean sees something like `a ^ b ^ c`, it will first parse the `a ^ b`
and then attempt to keep parsing (as long as precedence allows it) until
it cannot continue anymore. Hence Lean will parse this expression as `a ^ (b ^ c)`
(as we would expect it to).

--#--
この節の最後のコメント：Lean は常に可能な限り広いマッチを行おうと試行します。これは3つの重要な意味を持ちます。まず非常に直観的なことですが、ある右結合演算子 `^` があり、Lean が `a ^ b ^ c` のような式を見た場合、まず `a ^ b` をパースし、（優先順位が許す限り）これ以上続けられなくなるまでパースを続けようとします。この結果 Lean はこの式を（読者が期待するように）`a ^ (b ^ c)` とパースします。

--#--
Secondly, if we have a notation where precedence does not allow to figure
out how the expression should be parenthesized, for example:
--#--
第二に、例えば優先順位によって式のどこに括弧が入るかわからないような記法がある場合、例えば以下のような場合を考えます：
-/

notation:65 lhs:65 " ~ " rhs:65 => (lhs - rhs)

/-!
--#--
An expression like `a ~ b ~ c` will be parsed as `a ~ (b ~ c)` because
Lean attempts to find the longest parse possible. As a general rule of thumb:
If precedence is ambiguous Lean will default to right associativity.
--#--
`a ~ b ~ c` のような式は `a ~ (b ~ c)` としてパースされます。これは Lean が可能な限り広い範囲のパースを見つけようとするからです。一般的な経験則として：優先順位が曖昧な場合、Lean はデフォルトで右結合を使用します。
-/

#eval 5 ~ 3 ~ 3 -- 5 because this is parsed as 5 - (3 - 3)

/-!
--#--
Lastly, if we define overlapping notation such as:
--#--
最後に、下記のような既存のものに被る記法を定義しようとした場合：
-/

--#--
-- define `a ~ b mod rel` to mean that a and b are equivalent with respect to some equivalence relation rel
--#--
-- `a ~ b mod rel` を、ある同値関係 rel に関して a と b が同値であることとして定義
notation:65 a:65 " ~ " b:65 " mod " rel:65 => rel a b

/-!
--#--
Lean will prefer this notation over parsing `a ~ b` as defined above and
then erroring because it doesn't know what to do with `mod` and the
relation argument:
--#--
ここで Lean は `a ~ b` について、先ほどの定義でパースしてしまって `mod` と関係についての引数をどうしたらよいかわからずにエラーにしてしまうよりも、この記法を利用したいでしょう：
-/

#check 0 ~ 0 mod Eq -- 0 = 0 : Prop

/-!
--#--
This is again because it is looking for the longest possible parser which
in this case involves also consuming `mod` and the relation argument.
--#--
ここでも可能な限り最長のパーサを探すため、`mod` とその関係についての引数を消費します。
-/

/-!
--#--
### Free form syntax declarations
--#--
### 自由形式の構文宣言
--#--
With the above `infix` and `notation` commands, you can get quite far with
declaring ordinary mathematical syntax already. Lean does however allow you to
introduce arbitrarily complex syntax as well. This is done using two main commands
`syntax` and `declare_syntax_cat`. A `syntax` command allows you add a new
syntax rule to an already existing so-called "syntax category". The most common syntax
categories are:
- `term`, this category will be discussed in detail in the elaboration chapter,
  for now you can think of it as "the syntax of everything that has a value"
- `command`, this is the category for top-level commands like `#check`, `def` etc.
--#--
上記の `infix` と `notation` コマンドを使えば、普通の数学構文を宣言するだけで、すでにかなり遠くまで行けるようになります。しかし、Lean では任意で複雑な構文を導入することもできます。これには `syntax` と `declare_syntax_cat` コマンドを使います。`syntax` コマンドを使うと、既存のいわゆる「構文カテゴリ」に新しい構文ルールを追加することができます。最も一般的な構文カテゴリは以下の通りです：
- `term`、このカテゴリについてはエラボレーションの章で詳しく説明しますが、今のところは「値を持つすべてのもののための構文」と考えておけば良いです。
- `command`、これは `#check` や `def` などのトップレベルコマンドのカテゴリです。
- TODO: ...

--#--
Let's see this in action:
--#--
これらを実際に見てみましょう：
-/

syntax "MyTerm" : term

/-!
--#--
We can now write `MyTerm` in place of things like `1 + 1` and it will be
*syntactically* valid, this does not mean the code will compile yet,
it just means that the Lean parser can understand it:
--#--
これで `1 + 1` などの代わりに `MyTerm` と書くことができ、**構文的に** （syntactically）有効になります。これはコードがコンパイルできる状態であるという意味ではなく、Lean のパーサがそれを理解できるという意味です：
-/

#check_failure MyTerm
-- elaboration function for 'termMyTerm' has not been implemented
--   MyTerm

/-!
--#--
Note: `#check_failure` command allows incorrectly typed terms to be indicated without error.
--#--
注意：`#check_failure` コマンドを使用すると、型付けが正しくない項をエラー無く表示できます。
-/

/-!
--#--
Implementing this so-called "elaboration function", which will actually
give meaning to this syntax in terms of Lean's fundamental `Expr` type,
is topic of the elaboration chapter.

--#--
このいわゆる「エラボレーション関数」の実装は、Lean の基本的な型 `Expr` の観点からこの構文に実際の意味を与えるものであり、エラボレーションの章で扱う話題です。

--#--
The `notation` and `infix` commands are utilities that conveniently bundle syntax declaration
with macro definition (for more on macros, see the macro chapter),
where the contents left of the `=>` declare the syntax.
All the previously mentioned principles from `notation` and `infix` regarding precedence
fully apply to `syntax` as well.

--#--
`notation` と `infix` コマンドは構文宣言とマクロ宣言（マクロについてはマクロの章を参照）を便利にまとめたユーティリティであり、`=>` の左側の内容で構文を宣言します。前に述べた `notation` と `infix` の優先順位に関する原則はすべて `syntax` にも適用されます。

--#--
We can, of course, also involve other syntax into our own declarations
in order to build up syntax trees. For example, we could try to build our
own little boolean expression language:
--#--
もちろん、構文木を構築するために、他の構文を独自の宣言に含めることも可能です。例えば、小さな真偽値の表現言語を作ってみることもできます：
-/

namespace Playground2

--#--
-- The scoped modifier makes sure the syntax declarations remain in this `namespace`
-- because we will keep modifying this along the chapter
--#--
-- このスコープ修飾子によって、これらの構文宣言がこの `namespace` の中のみに閉じられるようになります。
-- というのもこれらの構文はこの章でこの後も変更するからです。
scoped syntax "⊥" : term -- ⊥ for false
scoped syntax "⊤" : term -- ⊤ for true
scoped syntax:40 term " OR " term : term
scoped syntax:50 term " AND " term : term
#check_failure ⊥ OR (⊤ AND ⊥) -- elaboration function hasn't been implemented but parsing passes

end Playground2

/-!
--#--
While this does work, it allows arbitrary terms to the left and right of our
`AND` and `OR` operation. If we want to write a mini language that only accepts
our boolean language on a syntax level we will have to declare our own
syntax category on top. This is done using the `declare_syntax_cat` command:
--#--
これは機能しますが、`AND` と `OR` 演算の左右に任意の項が置けてしまいます。もし構文レベルで真偽値言語だけを受け付けるミニ言語を書きたい場合は、独自の構文カテゴリを宣言する必要があります。これは `declare_syntax_cat` コマンドを使って行います：
-/

declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr -- ⊥ for false
syntax "⊤" : boolean_expr -- ⊤ for true
syntax:40 boolean_expr " OR " boolean_expr : boolean_expr
syntax:50 boolean_expr " AND " boolean_expr : boolean_expr

/-!
--#--
Now that we are working in our own syntax category, we are completely
disconnected from the rest of the system. And these cannot be used in place of
terms anymore:

--#--
これで独自の構文カテゴリにて作業するようになったため、システムの他の部分とは完全に切り離されました。そして、これらの構文はもはや任意の項で使うことができません：

```lean
#check ⊥ AND ⊤ -- expected term
```
-/

/-!
--#--
In order to integrate our syntax category into the rest of the system we will
have to extend an already existing one with new syntax, in this case we
will re-embed it into the `term` category:
--#--
この構文カテゴリをシステムの他の部分に統合するためには、既存の構文を新しい構文で拡張する必要があります。今回の場合は、`term` のカテゴリに再埋め込みします：
-/

syntax "[Bool|" boolean_expr "]" : term
#check_failure [Bool| ⊥ AND ⊤] -- elaboration function hasn't been implemented but parsing passes

/-!
--#--
### Syntax combinators
--#--
### 構文コンビネータ
--#--
In order to declare more complex syntax, it is often very desirable to have
some basic operations on syntax already built-in, these include:

--#--
より複雑な構文を宣言するためには、構文に対する基本的な操作がすでに組み込まれていることが望ましいことが多いです。これには以下が含まれます：

--#--
- helper parsers without syntax categories (i.e. not extendable)
- alternatives
- repetitive parts
- optional parts

--#--
- 構文カテゴリを持たない（つまり拡張できない）補助パーサ
- 選択肢
- 繰り返されるパーツ
- オプショナルなパーツ

--#--
While all of these do have an encoding based on syntax categories, this
can make things quite ugly at times, so Lean provides an easier way to do all
of these.

--#--
これらはすべて構文カテゴリに基づいたエンコーディングを持っていますが、場合によっては非常に不格好になることがあるため、Lean はこれらすべてを簡単に行う方法を提供しています。

--#--
In order to see all of these in action, we will briefly define a simple
binary expression syntax.
First things first, declaring named parsers that don't belong to a syntax
category is quite similar to ordinary `def`s:
--#--
これらすべての動作を確認するために、簡単なバイナリ式の構文を定義します。まず初めに、構文カテゴリに属さない名前付きパーサを宣言します。これは普通の `def` とよく似ています：
-/

syntax binOne := "O"
syntax binZero := "Z"

/-!
--#--
These named parsers can be used in the same positions as syntax categories
from above, their only difference to them is, that they are not extensible.
That is, they are directly expanded within syntax declarations,
and we cannot define new patterns for them as we would with proper syntax categories.
There does also exist a number of built-in named parsers that are generally useful,
most notably:
- `str` for string literals
- `num` for number literals
- `ident` for identifiers
--#--
これらの名前付き構文パーサは上記の構文カテゴリと同じ位置で使用することができますが、構文カテゴリとの唯一の違いは拡張性がないことです。つまり、構文宣言の中で直接展開されるため、適切な構文カテゴリのように新しいパターンを定義することができません。名前付きのパーサには一般的に便利な組み込みがいくつか存在しており、以下は特記に値するものです：
- 文字列リテラル用の `str`
- 数値リテラル用の `num`
- 識別子用の `ident`
- ... TODO: better list or link to compiler docs

--#--
Next up we want to declare a parser that understands digits, a binary digit is
either 0 or 1 so we can write:
--#--
次に数字を理解するパーサを宣言したいです。 2 進数の数字は 0 か 1 であるため、次のように書くことができます：
-/

syntax binDigit := binZero <|> binOne

/-!
--#--
Where the `<|>` operator implements the "accept the left or the right" behaviour.
We can also chain them to achieve parsers that accept arbitrarily many, arbitrarily complex
other ones. Now we will define the concept of a binary number, usually this would be written
as digits directly after each other but we will instead use comma separated ones to showcase
the repetition feature:
--#--
ここで `<|>` 演算子は「左右どちらかを受け入れる」動作を実装しています。また、これらを連鎖させて、任意の数・任意の複雑な他の構文を受け入れるパーサを実現することもできます。ここで 2 進数の概念を定義します。通常、 2 進数は数字を直接並べて書きますが、ここでは繰り返しを表現するためにカンマ区切りの表現を使います：
-/

--#--
-- the "+" denotes "one or many", in order to achieve "zero or many" use "*" instead
-- the "," denotes the separator between the `binDigit`s, if left out the default separator is a space
--#--
-- 「+」は「1以上」を示す。「0以上」を実現するには代わりに「*」を使う
-- 「,」は `binDigit` の間の区切り文字を示す。もし省略された場合、デフォルトの区切り文字はスペースになる
syntax binNumber := binDigit,+

/-!
--#--
Since we can just use named parsers in place of syntax categories, we can now easily
add this to the `term` category:

--#--
構文カテゴリの代わりに名前付きパーサを使えばよいため、これを `term` カテゴリに簡単に追加することができます：

```lean
syntax "bin(" binNumber ")" : term
#check bin(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
#check bin() -- fails to parse because `binNumber` is "one or many": expected 'O' or 'Z'
```
-/

syntax binNumber' := binDigit,* -- note the *
syntax "emptyBin(" binNumber' ")" : term
#check_failure emptyBin() -- elaboration function hasn't been implemented but parsing passes

/-!
--#--
Note that nothing is limiting us to only using one syntax combinator per parser,
we could also have written all of this inline:
--#--
パーサごとに 1 つの構文コンビネータしか使えないという制限は一切ないことに注意してください。これらをすべてインラインに記述することも可能です：
-/

syntax "binCompact(" ("Z" <|> "O"),+ ")" : term
#check_failure binCompact(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes

/-!
--#--
As a final feature, let's add an optional string comment that explains the binary
literal being declared:
--#--
最後の機能として、宣言されている 2 進数リテラルを説明するオプションの文字列コメントを追加しましょう：
-/

--#--
-- The (...)? syntax means that the part in parentheses is optional
--#--
-- (...)? 構文は括弧内がオプショナルであることを意味します
syntax "binDoc(" (str ";")? binNumber ")" : term
#check_failure binDoc(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
#check_failure binDoc("mycomment"; Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes

/-!
--#--
## Operating on Syntax
--#--
## 構文に対する操作
--#--
As explained above, we will not go into detail in this chapter on how to teach
Lean about the meaning you want to give your syntax. We will, however, take a look
at how to write functions that operate on it. Like all things in Lean, syntax is
represented by the inductive type `Lean.Syntax`, on which we can operate. It does
contain quite some information, but most of what we are interested in, we can
condense in the following simplified view:
--#--
上記で説明したように、この章では構文に与えたい意味を Lean に伝える方法については詳しく触れません。しかし、構文を操作する関数の書き方については見ていきます。Lean での他のものと同様に、構文は `Lean.Syntax` という帰納型によって表現されています。これによって構文を操作することが可能です。この型にはかなり多くの情報が含まれていますが、興味があることのほとんどは次のように単純化できます：
-/

namespace Playground2

inductive Syntax where
  | missing : Syntax
  | node (kind : Lean.SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom : String -> Syntax
  | ident : Lean.Name -> Syntax

end Playground2

/-!
--#--
Lets go through the definition one constructor at a time:
- `missing` is used when there is something the Lean compiler cannot parse,
  it is what allows Lean to have a syntax error in one part of the file but
  recover from it and try to understand the rest of it. This also means we pretty
  much don't care about this constructor.
- `node` is, as the name suggests, a node in the syntax tree. It has a so called
  `kind : SyntaxNodeKind` where `SyntaxNodeKind` is just a `Lean.Name`. Basically,
  each of our `syntax` declarations receives an automatically generated `SyntaxNodeKind`
  (we can also explicitly specify the name with `syntax (name := foo) ... : cat`) so
  we can tell Lean "this function is responsible for processing this specific syntax construct".
  Furthermore, like all nodes in a tree, it has children, in this case in the form of
  an `Array Syntax`.
- `atom` represents (with the exception of one) every syntax object that is at the bottom of the
  hierarchy. For example, our operators ` ⊕ ` and ` LXOR ` from above will be represented as
  atoms.
- `ident` is the mentioned exception to this rule. The difference between `ident` and `atom`
  is also quite obvious: an identifier has a `Lean.Name` instead of a `String` that represents it.
  Why a `Lean.Name` is not just a `String` is related to a concept called macro hygiene
  that will be discussed in detail in the macro chapter. For now, you can consider them
  basically equivalent.

--#--
コンストラクタの定義を1つずつ見ていきましょう：
- `missing` は Lean のコンパイラによってパースできないようなものがある際に使われます。このおかげで Lean はファイルの一部で構文エラーがあっても、そこから回復してファイルの残りの部分を理解しようとします。これはまた、このコンストラクタはあまり気にされないものであるということでもあります。
- `node` は名前の通り、構文木のノードです。ノードは `kind : SyntaxNodeKind` と呼ばれるものを持っています。この `SyntaxNodeKind` はただの `Lean.Name` です。基本的に、各 `syntax` 宣言は自動的に生成された `SyntaxNodeKind` を受け取り（この名前は `syntax (name := foo) ... : cat` で明示的に指定することもできます）、これによって Lean に「この関数は特定の構文構築を行う責任がある」ということを伝えます。さらに、木の中の全てのノードと同様に、この関数にも子があり、この場合は `Array Syntax` をいう形式をとっています。
- `atom` は（1つを除いて）階層の一番下にあるすべての構文オブジェクトを表します。例えば、上の演算子 ` ⊕ ` と ` LXOR ` は atom として表現されます。
- `ident` は `atom` で前述したこのルールの例外です。`ident` と `atom` の違いは実に明白です：識別子はそれを表すにあたって `String` の代わりに `Lean.Name` を持ちます。なぜ `Lean.Name` が単なる `String` ではないのかはマクロの章で詳しく説明するマクロの健全性（macro hygiene）と呼ばれる概念に関連しています。今のところ、これらは基本的に等価であると考えることができます。

--#--
### Constructing new `Syntax`
--#--
### 新しい `Syntax` の構築
--#--
Now that we know how syntax is represented in Lean, we could of course write programs that
generate all of these inductive trees by hand, which would be incredibly tedious and is something
we most definitely want to avoid. Luckily for us there is quite an extensive API hidden inside the
`Lean.Syntax` namespace we can explore:
--#--
Lean で構文がどのように表現されるか学んだので、もちろんのことながらこれらの帰納的な木をすべて手作業で生成するプログラムを書くことができますが、これは恐ろしく退屈であり間違いなく最高に避けたい作業です。幸運なことに、`Lean.Syntax` 名前空間には非常に広範囲な API が秘められています：
-/

open Lean
#check Syntax -- Syntax. autocomplete

/-!
--#--
The interesting functions for creating `Syntax` are the `Syntax.mk*` ones that allow us to create
both very basic `Syntax` objects like `ident`s but also more complex ones like `Syntax.mkApp`
which we can use to create the `Syntax` object that would amount to applying the function
from the first argument to the argument list (all given as `Syntax`) in the second one.
Let's see a few examples:
--#--
`Syntax` を作るための興味深い関数は `Syntax.mk*` で、`ident`のような基本的な `Syntax` オブジェクトの作成だけでなく、 `Syntax.mkApp` による複雑なオブジェクトも作成することができます。`Syntax.mkApp` によって、第1引数の関数を第2引数の引数リスト（すべて `Syntax` として与えられます）に適用することに相当する `Syntax` オブジェクトを作成することができます。いくつか例を見てみましょう：
-/

--#--
-- Name literals are written with this little ` in front of the name
--#--
-- 名前のリテラルは名前の前にちょっと ` を付けて書きます
#eval Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"] -- is the syntax of `Nat.add 1 1`
#eval mkNode `«term_+_» #[Syntax.mkNumLit "1", mkAtom "+", Syntax.mkNumLit "1"] -- is the syntax for `1 + 1`

--#--
-- note that the `«term_+_» is the auto-generated SyntaxNodeKind for the + syntax
--#--
-- `«term_+_» は + の構文用に自動生成された SyntaxNodeKind であることに注意

/-
--#--
If you don't like this way of creating `Syntax` at all you are not alone.
However, there are a few things involved with the machinery of doing this in
a pretty and correct (the machinery is mostly about the correct part) way
which will be explained in the macro chapter.

--#--
もし読者が `Syntax` を作成するこの方法を全く好まないのあれば、著者も全く同感です。しかし、これを綺麗で正しい方法で行うための機構（上記の機構はだいたい正しい部分を担います）は、マクロの章でもいくつか説明します。

--#--
### Matching on `Syntax`
--#--
### `Syntax` に対するマッチ
--#--
Just like constructing `Syntax` is an important topic, especially
with macros, matching on syntax is equally (or in fact even more) interesting.
Luckily we don't have to match on the inductive type itself either: we can
instead use so-called "syntax patterns". They are quite simple, their syntax is just
`` `(the syntax I want to match on) ``. Let's see one in action:
--#--
`Syntax` の構築が重要なトピックであるように、特にマクロでは構文のマッチも同様に（あるいは実はそれ以上に）興味深いものです。幸運なことに、帰納型自体でマッチする必要はありません：その代わりにいわゆる「構文パターン」を使います。これらは非常にシンプルで、その構文はただ `` `(the syntax I want to match on) `` とするだけです。実際に使ってみましょう：
-/

def isAdd11 : Syntax → Bool
  | `(Nat.add 1 1) => true
  | _ => false

#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- true
#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- false

/-!
--#--
The next level with matches is to capture variables from the input instead
of just matching on literals, this is done with a slightly fancier-looking syntax:
--#--
マッチの次のレベルはリテラルにマッチするだけでなく、入力から変数をキャプチャすることです。これは少しファンシーな見た目の構文で行われます：
-/

def isAdd : Syntax → Option (Syntax × Syntax)
  | `(Nat.add $x $y) => some (x, y)
  | _ => none

#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo]) -- none

/-!
--#--
### Typed Syntax
--#--
### 型付けされた構文
--#--
Note that `x` and `y` in this example are of type `` TSyntax `term ``, not `Syntax`.
Even though we are pattern matching on `Syntax` which, as we can see in the constructors,
is purely composed of types that are not `TSyntax`, so what is going on?
Basically the `` `() `` Syntax is smart enough to figure out the most general
syntax category the syntax we are matching might be coming from (in this case `term`).
It will then use the typed syntax type `TSyntax` which is parameterized
by the `Name` of the syntax category it came from. This is not only more
convenient for the programmer to see what is going on, it also has other
benefits. For Example if we limit the syntax category to just `num`
in the next example Lean will allow us to call `getNat` on the resulting
`` TSyntax `num `` directly without pattern matching or the option to panic:
--#--
この例の `x` と `y` は `Syntax` ではなく `` TSyntax `term `` 型であることに注意してください。コンストラクタを見ればわかるように、完璧に `TSyntax` ではない型だけで構成されている `Syntax` に対してパターンマッチしたのにも関わらずにこうなってしまっているのは、いったい何が起こっているのでしょうか？基本的に、`` `() `` 構文は賢いため、マッチする構文からくる可能性のあるもの（この場合は `term`）の中で最も一般的な構文カテゴリを把握することができます。この時に型付けされた構文型 `TSyntax` が用いられます。これはそれのもとになった構文カテゴリの `Name` でパラメータ化されています。これはプログラマにとって何が起こっているのかを確認するために便利なだけでなく、他にも利点があります。例えば、次の例で構文カテゴリを `num` に限定すると、Lean はパターンマッチやパニックのオプション無しで、結果の `` TSyntax `num `` に対して直接 `getNat` を呼び出すことができます：
-/

--#--
-- Now we are also explicitly marking the function to operate on term syntax
--#--
-- ここで項の構文を操作する関数を明示的にマークしている
def isLitAdd : TSyntax `term → Option Nat
  | `(Nat.add $x:num $y:num) => some (x.getNat + y.getNat)
  | _ => none

#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some 2
#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- none

/-!
--#--
If you want to access the `Syntax` behind a `TSyntax` you can do this using
`TSyntax.raw` although the coercion machinery should just work most of the time.
We will see some further benefits of the `TSyntax` system in the macro chapter.

--#--
`TSyntax` の裏にある `Syntax` にアクセスしたい場合は、`TSyntax.raw` で可能ですが、ほとんどの場合は型強制でうまくいきます。その他の `TSyntax` システムの恩恵についてはマクロの章で見ていきます。

--#--
One last important note about the matching on syntax: In this basic
form it only works on syntax from the `term` category. If you want to use
it to match on your own syntax categories you will have to use `` `(category| ...)``.

--#--
構文の機構について最後に大事な注意を：この基本的な形式では、`term` カテゴリからの構文にのみしか機能しません。これを自前の構文カテゴリに使いたい場合は `` `(category| ...)`` を使う必要があります。

--#--
### Mini Project
--#--
### 小さいプロジェクト
--#--
As a final mini project for this chapter we will declare the syntax of a mini
arithmetic expression language and a function of type `Syntax → Nat` to evaluate
it. We will see more about some of the concepts presented below in future
chapters.
--#--
本章での最後のミニプロジェクトとして、算術式についての小さな言語の構文とそれを評価する `Syntax → Nat` 型の関数を定義します。以下のコンセプトについては今後の章でさらに見ていきます。
-/

declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith

partial def denoteArith : TSyntax `arith → Nat
  | `(arith| $x:num) => x.getNat
  | `(arith| $x:arith + $y:arith) => denoteArith x + denoteArith y
  | `(arith| $x:arith - $y:arith) => denoteArith x - denoteArith y
  | `(arith| ($x:arith)) => denoteArith x
  | _ => 0

--#--
-- You can ignore Elab.TermElabM, what is important for us is that it allows
-- us to use the ``(arith| (12 + 3) - 4)` notation to construct `Syntax`
-- instead of only being able to match on it like this.
--#--
-- Elab.TermElabM は無視することができる。
-- ここで重要なことは、 `Syntax` を構築するにあたって以下のようにマッチすることができるだけでなく
-- ``(arith| (12 + 3) - 4)` という記法を使うことができる。
def test : Elab.TermElabM Nat := do
  let stx ← `(arith| (12 + 3) - 4)
  pure (denoteArith stx)

#eval test -- 11

/-!
--#--
Feel free to play around with this example and extend it in whatever way
you want to. The next chapters will mostly be about functions that operate
on `Syntax` in some way.
--#--
この例を自由に弄って好きなように拡張してみてください。次の章では、主に `Syntax` を何らかの方法で操作する関数について説明します。
-/

/-!
--#--
## More elaborate examples
--#--
## エラボレートのさらなる例
--#--
### Using type classes for notations
--#--
### 記法のための型クラスの利用
--#--
We can use type classes in order to add notation that is extensible via
the type instead of the syntax system, this is for example how `+`
using the typeclasses `HAdd` and `Add` and other common operators in
Lean are generically defined.

--#--
構文システムの代わりに、型システムを通じた記法を追加するために型クラスを使うことができます。これは例えば、型クラス `HAdd` と `Add` を使った `+` や、など Lean のその他の共通の演算子の一般的な定義方法などです。

--#--
For example, we might want to have a generic notation for subset notation.
The first thing we have to do is define a type class that captures
the function we want to build notation for.
--#--
例えば、部分集合記法のための一般的な記法が欲しいとしましょう。まず初めにすべきことは、この記法を確立したい関数を備えた型クラスを定義することです。
-/

class Subset (α : Type u) where
  subset : α → α → Prop

/-!
--#--
The second step is to define the notation, what we can do here is simply
turn every instance of a `⊆` appearing in the code to a call to `Subset.subset`
because the type class resolution should be able to figure out which `Subset`
instance is referred to. Thus the notation will be a simple:
--#--
次のステップは記法の定義です。ここでできることは、単純にコード中に現れる `⊆` のインスタンスをすべて `Subset.subset` の呼び出しに置き換えることです。というのも型クラスの解決によってどの `Subset` インスタンスが参照されているかを把握することができるからです。したがって記法はシンプルになります：
-/

--#--
-- precedence is arbitrary for this example
--#--
-- この例の優先順位は任意
infix:50 " ⊆ " => Subset.subset

/-!
--#--
Let's define a simple theory of sets to test it:
--#--
これを検証するために簡単な集合論を定義してみましょう：
-/

--#--
-- a `Set` is defined by the elements it contains
-- -> a simple predicate on the type of its elements
--#--
-- `Set` はそれを保持する要素によって定義される
-- -> その要素の型に対するシンプルな述語
def Set (α : Type u) := α → Prop

def Set.mem (x : α) (X : Set α) : Prop := X x

--#--
-- Integrate into the already existing typeclass for membership notation
--#--
-- 既存の要素の所属の記法の型クラスへと統合
instance : Membership α (Set α) where
  mem := Set.mem

def Set.empty : Set α := λ _ => False

instance : Subset (Set α) where
  subset X Y := ∀ (x : α), x ∈ X → x ∈ Y

example : ∀ (X : Set α), Set.empty ⊆ X := by
  intro X x
  -- ⊢ x ∈ Set.empty → x ∈ X
  intro h
  exact False.elim h -- empty set has no members

/-!
--#--
### Binders
--#--
### 束縛子
--#--
Because declaring syntax that uses variable binders used to be a rather
unintuitive thing to do in Lean 3, we'll take a brief look at how naturally
this can be done in Lean 4.

--#--
変数の束縛子を使用する構文を宣言することは Lean 3 ではかなり非直観的でしたが、Lean 4 ではどのように自然にできるかを簡単に見てみましょう。

--#--
For this example we will define the well-known notation for the set
that contains all elements `x` such that some property holds:
`{x ∈ ℕ | x < 10}` for example.

--#--
この例では、ある性質が成り立つようなすべての要素 `x` を含む集合のよく知られた記法を定義します：例えば `{x ∈ ℕ | x < 10}` です。

--#--
First things first we need to extend the theory of sets from above slightly:
--#--
まず最初に、上記の集合論を少し拡張する必要があります：
-/

--#--
-- the basic "all elements such that" function for the notation
--#--
-- 「～であるようなすべての要素」という基本的な関数のための記法
def setOf {α : Type} (p : α → Prop) : Set α := p

/-!
--#--
Equipped with this function, we can now attempt to intuitively define a
basic version of our notation:
--#--
この関数を用いて、この記法の基本的なバージョンを直観的に定義することができます：
-/
notation "{ " x " | " p " }" => setOf (fun x => p)

#check { (x : Nat) | x ≤ 1 } -- { x | x ≤ 1 } : Set Nat

example : 1 ∈ { (y : Nat) | y ≤ 1 } := by simp[Membership.mem, Set.mem, setOf]
example : 2 ∈ { (y : Nat) | y ≤ 3 ∧ 1 ≤ y } := by simp[Membership.mem, Set.mem, setOf]

/-!
--#--
This intuitive notation will indeed deal with what we could throw at
it in the way we would expect it.

--#--
この直観的な記法は期待通りの形で渡されるものに対処することができます。

--#--
As to how one might extend this notation to allow more set-theoretic
things such as `{x ∈ X | p x}` and leave out the parentheses around
the bound variables, we refer the reader to the macro chapter.

--#--
この記法を拡張して `{x ∈ X | p x}` のような集合論的な書き方を許可し、束縛変数の周りの括弧を省く方法についてはマクロの章を参照してください。

--#--

## Exercises

--#--
## 演習問題

--#--
1. Create an "urgent minus 💀" notation such that `5 * 8 💀 4` returns `20`, and `8 💀 6 💀 1` returns `3`.

--#--
1. `5 * 8 💀 4` が `20` を、`8 💀 6 💀 1` が `3` を返すような「緊急マイナス 💀」記法を作ってください。

--#--
    **a)** Using `notation` command.
    **b)** Using `infix` command.
    **c)** Using `syntax` command.

--#--
    **a)** `notation` コマンドを使う場合。
    **b)** `infix` コマンドを使う場合。
    **c)** `syntax` コマンドを使う場合。

--#--
    Hint: multiplication in Lean 4 is defined as `infixl:70 " * " => HMul.hMul`.

--#--
    ヒント：Lean 4 の乗算は `infixl:70 " * " => HMul.hMul` で定義されています。

--#--
2. Consider the following syntax categories: `term`, `command`, `tactic`; and 3 syntax rules given below. Make use of each of these newly defined syntaxes.

--#--
2. 以下の構文カテゴリを考えてみましょう：`term`・`command`・`tactic`；そして以下に示す 3 つの構文ルールについて、これらの新しく定義された構文をそれぞれ使ってみましょう。

    ```lean
      syntax "good morning" : term
      syntax "hello" : command
      syntax "yellow" : tactic
    ```

--#--
3. Create a `syntax` rule that would accept the following commands:

--#--
3. 以下のコマンドを許容する `syntax` ルールを作ってください：

    - `red red red 4`
    - `blue 7`
    - `blue blue blue blue blue 18`

--#--
    (So, either all `red`s followed by a number; or all `blue`s followed by a number; `red blue blue 5` - shouldn't work.)

--#--
    （つまり、複数の `red` の後に数字が来るか；あるいは複数の `blue` の後に数字が来るか；`red blue blue 5` は機能しません。）

--#--
    Use the following code template:

--#--
    以下のコードテンプレートを使用してください：


    ```lean
    syntax (name := colors) ...
    -- our "elaboration function" that infuses syntax with semantics
    @[command_elab colors] def elabColors : CommandElab := λ stx => Lean.logInfo "success!"
    ```

--#--
4. Mathlib has a `#help option` command that displays all options available in the current environment, and their descriptions. `#help option pp.r` will display all options starting with a "pp.r" substring.

--#--
4. Mathlib には `#help option` コマンドがあり、現在の環境で利用可能なすべてのオプションとその説明を表示します。`#help option pp.r` は部分文字列「pp.r」で始まるすべてのオプションを表示します。

--#--
    Create a `syntax` rule that would accept the following commands:

--#--
    以下のコマンドを許容する `syntax` ルールを作ってください：

    - `#better_help option`
    - `#better_help option pp.r`
    - `#better_help option some.other.name`

--#--
    Use the following template:

--#--
    以下のテンプレートを使用してください：

    ```lean
    syntax (name := help) ...
    -- our "elaboration function" that infuses syntax with semantics
    @[command_elab help] def elabHelp : CommandElab := λ stx => Lean.logInfo "success!"
    ```

--#--
5. Mathlib has a ∑ operator. Create a `syntax` rule that would accept the following terms:

--#--
5. Mathlib には ∑ 演算子があります。以下の項を許容する `syntax` ルールを作ってください：

    - `∑ x in { 1, 2, 3 }, x^2`
    - `∑ x in { "apple", "banana", "cherry" }, x.length`

--#--
    Use the following template:

--#--
    以下のテンプレートを使用してください：

    ```lean
    import Std.Classes.SetNotation
    import Std.Util.ExtendedBinder
    syntax (name := bigsumin) ...
    -- our "elaboration function" that infuses syntax with semantics
    @[term_elab bigsumin] def elabSum : TermElab := λ stx tp => return mkNatLit 666
    ```

--#--
    Hint: use the `Std.ExtendedBinder.extBinder` parser.
    Hint: you need Std4 installed in your Lean project for these imports to work.

--#--
    ヒント：`Std.ExtendedBinder.extBinder` パーサを使ってください。
    ヒント：これらの import を機能させるには読者の Lean プロジェクトに batteries をインストールする必要があります。

-/
