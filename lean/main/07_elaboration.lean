/-
--#--
# Elaboration

--#--
# エラボレーション

--#--
The elaborator is the component in charge of turning the user facing
`Syntax` into something with which the rest of the compiler can work.
Most of the time, this means translating `Syntax` into `Expr`s but
there are also other use cases such as `#check` or `#eval`. Hence the
elaborator is quite a large piece of code, it lives
[here](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab).

--#--
エラボレータは、ユーザが目にする `Syntax` をコンパイラの他の部分がそれを処理できるようなものに変換するコンポーネントです。ほとんどの場合、これは `Syntax` を `Expr` に変換することを意味しますが、`#check` や `#eval` のような他の使用例もあります。このためエラボレータは非常に大きなコードとなっており、[ここ](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab) に格納されています。

--#--
## Command elaboration
--#--
## コマンドのエラボレーション
--#--
A command is the highest level of `Syntax`, a Lean file is made
up of a list of commands. The most commonly used commands are declarations,
for example:
--#--
コマンドは `Syntax` の最上位レベルであり、Lean ファイルはコマンドのリストで構成されます。最もよく使われるコマンドは宣言であり、例えば以下です：

- `def`
- `inductive`
- `structure`

--#--
but there are also other ones, most notably `#check`, `#eval` and friends.
All commands live in the `command` syntax category so in order to declare
custom commands, their syntax has to be registered in that category.

--#--
しかし、これ以外にもコマンドは存在しており、特筆すべきなものとして `#check` や `#eval` などのタイプです。すべてのコマンドは `command` という構文カテゴリに属しているため、カスタムコマンドを宣言するには、その構文をそのカテゴリに登録する必要があります。

--#--
### Giving meaning to commands
--#--
### コマンドに意味を与える
--#--
The next step is giving some semantics to the syntax. With commands, this
is done by registering a so called command elaborator.

--#--
次のステップは構文にセマンティクスを与えることです。コマンドの場合、これはいわゆるコマンドエラボレータを登録することで行われます。

--#--
Command elaborators have type `CommandElab` which is an alias for:
`Syntax → CommandElabM Unit`. What they do, is take the `Syntax` that
represents whatever the user wants to call the command and produce some
sort of side effect on the `CommandElabM` monad, after all the return
value is always `Unit`. The `CommandElabM` monad has 4 main kinds of
side effects:
1. Logging messages to the user via the `Monad` extensions
   `MonadLog` and `AddMessageContext`, like `#check`. This is done via
   functions that can be found in `Lean.Elab.Log`, the most notable ones
   being: `logInfo`, `logWarning` and `logError`.
2. Interacting with the `Environment` via the `Monad` extension `MonadEnv`.
   This is the place where all of the relevant information for the compiler
   is stored, all known declarations, their types, doc-strings, values etc.
   The current environment can be obtained via `getEnv` and set via `setEnv`
   once it has been modified. Note that quite often wrappers around `setEnv`
   like `addDecl` are the correct way to add information to the `Environment`.
3. Performing `IO`, `CommandElabM` is capable of running any `IO` operation.
   For example reading from files and based on their contents perform
   declarations.
4. Throwing errors, since it can run any kind of `IO`, it is only natural
   that it can throw errors via `throwError`.

--#--
コマンドエラボレータは `CommandElab` という型を持っており、これは `Syntax → CommandElabM Unit` という型のエイリアスです。これがすることは、コマンドが呼ばれた際に期待されるものを表現した `Syntax` を取り、`CommandElabM` モナド上の副作用を生み出します。最終的な戻り値は `Unit` です。`CommandElabM` モナドには主に4種類の副作用があります：

1. `Monad` を拡張した `MonadLog` と `AddMessageContext` を使って `#check` のようにユーザにメッセージをログ出力する。これは `Lean.Elab.Log` にある関数で行われ、特に有名なものは `logInfo`・`logWarning`・`logError` です。
2. `Monad` を拡張した `MonadEnv` を使って `Environment` とやり取りする。これはコンパイラに関連するすべての情報が格納される場所であり、すべての既知の宣言・その型・ドキュメント文字列・値などが格納されています。現在の環境は `getEnv` で取得でき、更新は `setEnv` で設定できます。ここで `Environment` に情報を追加するにあたっては `setEnv` のラッパーである `addDecl` などを用いることが大体において正しい方法であることに注意してください。
3. `IO` の実行。`CommandElabM` はあらゆる `IO` 操作を実行することができます。例えば、ファイルを読み込んでその内容に基づいて宣言を行うことができます。
4. 例外の送出。このモナドはどんな `IO` でも実行できるため、例外を `throwError` で投げることは自然です。

--#--
Furthermore there are a bunch of other `Monad` extensions that are supported
by `CommandElabM`:
- `MonadRef` and `MonadQuotation` for `Syntax` quotations like in macros
- `MonadOptions` to interact with the options framework
- `MonadTrace` for debug trace information
- TODO: There are a few others though I'm not sure whether they are relevant,
  see the instance in `Lean.Elab.Command`

--#--
さらに、`CommandElabM` がサポートする `Monad` の拡張はほかにもたくさんあります：

- マクロと同じような `Syntax` quotation 用の `MonadRef` と `MonadQuotation`
- オプションのフレームワークとのやり取りのための `MonadOptions`
- デバッグトレースの情報のための `MonadTrace`
- TODO: 関連性があるかどうかはわかりませんが、他にもいくつかあります。`Lean.Elab.Command` のインスタンスを参照してください。

--#--
### Command elaboration
--#--
### コマンドのエラボレーション
--#--
Now that we understand the type of command elaborators let's take a brief
look at how the elaboration process actually works:
1. Check whether any macros can be applied to the current `Syntax`.
   If there is a macro that does apply and does not throw an error
   the resulting `Syntax` is recursively elaborated as a command again.
2. If no macro can be applied, we search for all `CommandElab`s that have been
   registered for the `SyntaxKind` of the `Syntax` we are elaborating,
   using the `command_elab` attribute.
3. All of these `CommandElab` are then tried in order until one of them does not throw an
   `unsupportedSyntaxException`, Lean's way of indicating that the elaborator
   "feels responsible"
   for this specific `Syntax` construct. Note that it can still throw a regular
   error to indicate to the user that something is wrong. If no responsible
   elaborator is found, then the command elaboration is aborted with an `unexpected syntax`
   error message.

--#--
さて、コマンドエラボレータの種類を理解したところで、エラボレーションのプロセスが実際にどのように機能するのかを簡単に見てみましょう。
1. 現在の `Syntax` に適用できるマクロがあるかどうかをチェックする。適用可能なマクロがあり、例外が投げられなければ、結果の `Syntax` がコマンドとして再帰的にエラボレートされます。
2. マクロを適用できない場合は、エラボレートする `Syntax` の `SyntaxKind` に対して登録されているすべての `CommandElab` を検索する。これは `command_elab` 属性を使用して登録されています。
3. これらの `CommandElab` はすべて `unsupportedSyntaxException` を投げるものが出現するまで順番に試行されます。これは、そのエラボレータがこの特定の `Syntax` の構築に対して「責任を負っている」ことを示す Lean 流の方法です。これらのエラボレータは何かが間違っていることをユーザに示すために通常の例外を投げうることに注意してください。責任を持つエラボレータが見つからない場合、コマンドのエラボレーションは `unexpected syntax` エラーメッセージとともに中断されます。

--#--
As you can see the general idea behind the procedure is quite similar to ordinary macro expansion.

--#--
見てわかるように、この手順の背後にある一般的な考え方は通常のマクロ展開とよく似ています。

--#--
### Making our own
--#--
### 自分用のものを作る
--#--
Now that we know both what a `CommandElab` is and how they are used, we can
start looking into writing our own. The steps for this, as we learned above, are:
1. Declaring the syntax
2. Declaring the elaborator
3. Registering the elaborator as responsible for the syntax via the `command_elab`
   attribute.

--#--
これで `CommandElab` とは何か、そしてそれがどのように使われるかわかったので、次は自分用のものを作る方法に着目します。そのための手順は上で学んだとおりです：
1. 構文を定義する
2. エラボレータを定義する
3. `command_elab` 属性を用いて、構文を担当するエラボレータを登録する。

--#--
Let's see how this is done:
--#--
これがどのように実現されるか見てみましょう：
-/

import Lean

open Lean Elab Command Term Meta

syntax (name := mycommand1) "#mycommand1" : command -- declare the syntax

@[command_elab mycommand1]
def mycommand1Impl : CommandElab := fun stx => do -- declare and register the elaborator
  logInfo "Hello World"

#mycommand1 -- Hello World

/-!
--#--
You might think that this is a little boiler-platey and it turns out the Lean
devs did as well so they added a macro for this!
--#--
これは少々ボイラープレート的だと思われるかもしれませんが、Lean の開発者もそう思っていたようです。そこで彼らはこれのためのマクロを追加しました！
-/
elab "#mycommand2" : command =>
  logInfo "Hello World"

#mycommand2 -- Hello World

/-!
--#--
Note that, due to the fact that command elaboration supports multiple
registered elaborators for the same syntax, we can in fact overload
syntax, if we want to.
--#--
コマンドのエラボレーションは同じ構文に対して複数のエラボレータの登録をサポートしているため、必要な時には実は構文のオーバーロードが可能である点に注意してください。
-/
@[command_elab mycommand1]
def myNewImpl : CommandElab := fun stx => do
  logInfo "new!"

#mycommand1 -- new!

/-!
--#--
Furthermore it is also possible to only overload parts of syntax by
throwing an `unsupportedSyntaxException` in the cases we want the default
handler to deal with it or just letting the `elab` command handle it.
--#--
さらに、`unsupportedSyntaxException` を投げることで、構文の一部だけをオーバーロードすることも可能で、その場合はデフォルトのハンドラに処理させるか、`elab` コマンドに処理を処理をまかせます。
-/

/-
--#--
In the following example, we are not extending the original `#check` syntax,
but adding a new `SyntaxKind` for this specific syntax construct.
However, from the point of view of the user, the effect is basically the same.
--#--
以下の例では、元の `#check` 構文を拡張しているのではなく、この特定の構文のために新しい `SyntaxKind` を追加しています。しかし利用者からすれば、このコマンドの効果は基本的に同じです。
-/
elab "#check" "mycheck" : command => do
  logInfo "Got ya!"

/-
--#--
This is actually extending the original `#check`
--#--
これは実際にはオリジナルの `#check` を拡張したものです。
-/
@[command_elab Lean.Parser.Command.check] def mySpecialCheck : CommandElab := fun stx => do
  if let some str := stx[1].isStrLit? then
    logInfo s!"Specially elaborated string literal!: {str} : String"
  else
    throwUnsupportedSyntax

#check mycheck -- Got ya!
#check "Hello" -- Specially elaborated string literal!: Hello : String
#check Nat.add -- Nat.add : Nat → Nat → Nat

/-!
--#--
### Mini project
--#--
### ミニプロジェクト
--#--
As a final mini project for this section let's build a command elaborator
that is actually useful. It will take a command and use the same mechanisms
as `elabCommand` (the entry point for command elaboration) to tell us
which macros or elaborators are relevant to the command we gave it.

--#--
この節の最後のミニプロジェクトとして、実際に役立つコマンドエラボレータを作ってみましょう。これはコマンドを受け取り、`elabCommand`（コマンドのエラボレーションのエントリポイント）と同じメカニズムを使って、与えたコマンドに関連するマクロやエラボレータを教えてくれます。

--#--
We will not go through the effort of actually reimplementing `elabCommand` though
--#--
しかし、実際に `elabCommand` を再実装する労力は省きます。
-/
elab "#findCElab " c:command : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  match macroRes with
  | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match elabs with
    | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
    | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"

#findCElab def lala := 12 -- Your syntax may be elaborated by: [Lean.Elab.Command.elabDeclaration]
#findCElab abbrev lolo := 12 -- Your syntax may be elaborated by: [Lean.Elab.Command.elabDeclaration]
#findCElab #check foo -- even our own syntax!: Your syntax may be elaborated by: [mySpecialCheck, Lean.Elab.Command.elabCheck]
#findCElab open Hi -- Your syntax may be elaborated by: [Lean.Elab.Command.elabOpen]
#findCElab namespace Foo -- Your syntax may be elaborated by: [Lean.Elab.Command.elabNamespace]
#findCElab #findCElab open Bar -- even itself!: Your syntax may be elaborated by: [«_aux_lean_elaboration___elabRules_command#findCElab__1»]

/-!
--#--
TODO: Maybe we should also add a mini project that demonstrates a
non # style command aka a declaration, although nothing comes to mind right now.
TODO:  Define a `conjecture` declaration, similar to `lemma/theorem`, except that
it is automatically sorried.  The `sorry` could be a custom one, to reflect that
the "conjecture" might be expected to be true.
--#--
TODO: 今すぐには何も思い浮かばないが、# スタイルではないコマンド、つまり宣言を示すミニプロジェクトも追加すべきかもしれない。
TODO: `lemma/theorem` に似ているが、自動的に sorry してくれる `conjecture` 宣言を定義する。`sorry` は「推測」が真であると予想されることを反映するために、カスタムのものにすることもできる。
-/

/-!
--#--
## Term elaboration
--#--
## 項のエラボレーション
--#--
A term is a `Syntax` object that represents some sort of `Expr`.
Term elaborators are the ones that do the work for most of the code we write.
Most notably they elaborate all the values of things like definitions,
types (since these are also just `Expr`) etc.

--#--
項はある種の `Expr` を表す `Syntax` オブジェクトです。項エラボレータは私たちが書くコードのほとんどを処理するものです。特に、定義や型（これらも単なる `Expr` であるため）など、すべての値をエラボレートします。

--#--
All terms live in the `term` syntax category (which we have seen in action
in the macro chapter already). So, in order to declare custom terms, their
syntax needs to be registered in that category.

--#--
すべての項は `term` 構文カテゴリに属しています（この動作はマクロの章ですでに見ています）。したがって、カスタムの項を宣言するには、その構文をこのカテゴリに登録する必要があります。

--#--
### Giving meaning to terms
--#--
### 項に意味を与える
--#--
As with command elaboration, the next step is giving some semantics to the syntax.
With terms, this is done by registering a so called term elaborator.

--#--
コマンドのエラボレーションと同様に、次のステップは構文にセマンティクスを与えることです。項の場合、これはいわゆる項エラボレータを登録することで行われます。

--#--
Term elaborators have type `TermElab` which is an alias for:
`Syntax → Option Expr → TermElabM Expr`. This type is already
quite different from command elaboration:
- As with command elaboration the `Syntax` is whatever the user used
  to create this term
- The `Option Expr` is the expected type of the term, since this cannot
  always be known it is only an `Option` argument
- Unlike command elaboration, term elaboration is not only executed
  because of its side effects -- the `TermElabM Expr` return value does
  actually contain something of interest, namely, the `Expr` that represents
  the `Syntax` object.

--#--
項エラボレータは `TermElab` という型を持っており、これは `Syntax → Option Expr → TermElabM Expr` という型のエイリアスです。この型の時点ですでにコマンドのエラボレーションとはかなり異なっています：
- コマンドのエラボレーションと同様に、この `Syntax` はユーザがこの項を作成するために使用したものです。
- `Option Expr` は期待される項の型ですが、これは常にわかるとは限らないため、`Option` 引数となっています。
- コマンドのエラボレーションとは異なり、項のエラボレーションはその副作用によって実行されるだけでなく、`TermElabM Expr` が戻り値には実際の興味の対象、つまりその `Syntax` オブジェクトを表す `Expr` を含んでいます。

--#--
`TermElabM` is basically an upgrade of `CommandElabM` in every regard:
it supports all the capabilities we mentioned above, plus two more.
The first one is quite simple: On top of running `IO` code it is also
capable of running `MetaM` code, so `Expr`s can be constructed nicely.
The second one is very specific to the term elaboration loop.

--#--
`TermElabM` は基本的にすべての点で `CommandElabM` をアップグレードしたものです：これは上述したものをすべてに加えてさらに2つの機能をサポートしています。一つ目は非常にシンプルです：`IO` コードを実行することに加えて、`MetaM` のコードも実行することができるため、`Expr` をうまく構築することができます。2つ目はエラボレーションのループという項に特化したものです。

--#--
### Term elaboration
--#--
### 項のエラボレーション
--#--
The basic idea of term elaboration is the same as command elaboration:
expand macros and recurse or run term elaborators that have been registered
for the `Syntax` via the `term_elab` attribute (they might in turn run term elaboration)
until we are done. There is, however, one special action that a term elaborator
can do during its execution.

--#--
項のエラボレーションの基本的なアイデアはコマンドのエラボレーションと同じです：マクロを展開し、`term_elab` 属性によって `Syntax` に登録された項エラボレータを全て完了するまで再帰的に実行します（`term_elab` 属性が項のエラボレーションを実行することもあります）。しかし、項エラボレータが実行中にできる特別なアクションが1つあります。

--#--
A term elaborator may throw `Except.postpone`. This indicates that
the term elaborator requires more
information to continue its work. In order to represent this missing information,
Lean uses so called synthetic metavariables. As you know from before, metavariables
are holes in `Expr`s that are waiting to be filled in. Synthetic metavariables are
different in that they have special methods that are used to solve them,
registered in `SyntheticMVarKind`. Right now, there are four of these:
- `typeClass`, the metavariable should be solved with typeclass synthesis
- `coe`, the metavariable should be solved via coercion (a special case of typeclass)
- `tactic`, the metavariable is a tactic term that should be solved by running a tactic
- `postponed`, the ones that are created at `Except.postpone`

--#--
項エラボレータは `Except.postpone` を投げることがあります。これは項エラボレータが作業を続けるためにさらなる情報を必要としていることを示します。この不足している情報を表現するために、Lean はいわゆる synthetic metavariable を使用します。以前からご存じのように、メタ変数は埋められることを待っている `Expr` の穴です。synthetic metavariable はそれを解決するための特別なメソッドを持っている点で異なっており、`SyntheticMVarKind` に登録されています。現時点では4種類あります：
- `typeClass`、メタ変数は型クラスの統合で解決される
- `coe`、メタ変数は強制によって解決される（型クラスの特殊なケース）
- `tactic`、メタ変数はタクティクの項であり、タクティクを実行することで解決される
- `postponed`、`Except.postpone` で生成される

--#--
Once such a synthetic metavariable is created, the next higher level term elaborator will continue.
At some point, execution of postponed metavariables will be resumed by the term elaborator,
in hopes that it can now complete its execution. We can try to see this in
action with the following example:
--#--
このような synthetic metavariable が作成されると、次の上位レベルの項エラボレータが継続されます。ある時点で延期されたメタ変数の実行は、その実行が完了できる望みができた時に項エラボレータによって再開されます。次の例でこれを実際に見てみましょう：
-/
#check set_option trace.Elab.postpone true in List.foldr .add 0 [1,2,3] -- [Elab.postpone] .add : ?m.5695 → ?m.5696 → ?m.5696

/-!
--#--
What happened here is that the elaborator for function applications started
at `List.foldr` which is a generic function so it created metavariables
for the implicit type parameters. Then, it attempted to elaborate the first argument `.add`.

--#--
ここで起こったことは、関数適用のエラボレータがジェネリックな関数である `List.foldr` に対して開始し、暗黙の型パラメータのメタ変数を作成したことです。そして最初の引数 `.add` をエラボレートしようとしました。

--#--
In case you don't know how `.name` works, the basic idea is that quite
often (like in this case) Lean should be able to infer the output type (in this case `Nat`)
of a function (in this case `Nat.add`).  In such cases, the `.name` feature will then simply
search for a function named `name` in the namespace `Nat`. This is especially
useful when you want to use constructors of a type without referring to its
namespace or opening it, but can also be used like above.

--#--
`.name` がどのように機能するかご存じでない方のために説明しておくと、基本的な考え方は大体（今回のケースのように）Lean が関数（今回の場合は `Nat.add`）の出力型（今回の場合は `Nat`）を推測できるべきというものです。このような場合、`.name` 機能は名前空間 `Nat` で `name` という名前の関数を単純に検索します。これはある型のコンストラクタをその名前空間を参照したり開いたりすることなく使用したい場合に特に便利ですが、上記のように使用することもできます。

--#--
Now back to our example, while Lean does at this point already know that `.add`
needs to have type: `?m1 → ?m2 → ?m2` (where `?x` is notation for a metavariable)
the elaborator for `.add` does need to know the actual value of `?m2` so the
term elaborator postpones execution (by internally creating a synthetic metavariable
in place of `.add`), the elaboration of the other two arguments then yields the fact that
`?m2` has to be `Nat` so once the `.add` elaborator is continued it can work with
this information to complete elaboration.

--#--
さて、例に戻ると Lean はこの時点で `.add` が型 `?m1 → ?m2 → ?m2`（ここで `?x` はメタ変数の記法です）を持つ必要があることを知っています。`.add` のエラボレータは `?m2` の実際の値を知る必要があるため、項エラボレータは実行を延期します（これは `.add` の代わりに内部的に synthetic metavariable を作成することで行われます）。他の2つの引数のエラボレーションによって `?m2` が `Nat` でなければならないという事実が得られるため、`.add` のエラボレータが続行されると、この情報を使ってエラボレーションを完了することができます。

--#--
We can also easily provoke cases where this does not work out. For example:
--#--
また、これがうまくいかないケースを引き起こすことも簡単にできます。例えば：
-/

#check_failure set_option trace.Elab.postpone true in List.foldr .add
-- [Elab.postpone] .add : ?m.5808 → ?m.5809 → ?m.5809
-- invalid dotted identifier notation, expected type is not of the form (... → C ...) where C is a constant
  -- ?m.5808 → ?m.5809 → ?m.5809

/-!
--#--
In this case `.add` first postponed its execution, then got called again
but didn't have enough information to finish elaboration and thus failed.

--#--
この場合、`.add` はまず実行を延期し、その後再び呼び出されましたが、エラボレーションを終えるのに十分な情報を持っていなかったことで失敗しました。

--#--
### Making our own
--#--
### 自分用のものを作る
--#--
Adding new term elaborators works basically the same way as adding new
command elaborators so we'll only take a very brief look:
--#--
新しい項エラボレータの追加は、新しいコマンドエラボレータの追加と基本的に同じように機能するため、ごく簡単に見ておきましょう：
-/

syntax (name := myterm1) "myterm 1" : term

def mytermValues := [1, 2]

@[term_elab myterm1]
def myTerm1Impl : TermElab := fun stx type? =>
  mkAppM ``List.get! #[.const ``mytermValues [], mkNatLit 0] -- `MetaM` code

#eval myterm 1 -- 1

--#--
-- Also works with `elab`
--#--
-- `elab` も機能する
elab "myterm 2" : term => do
  mkAppM ``List.get! #[.const ``mytermValues [], mkNatLit 1] -- `MetaM` code

#eval myterm 2 -- 2

/-!
--#--
### Mini project
--#--
### 小さなプロジェクト
--#--
As a final mini project for this chapter we will recreate one of the most
commonly used Lean syntax sugars, the `⟨a,b,c⟩` notation as a short hand
for single constructor types:
--#--
本章の最後のミニプロジェクトとして、最もよく使われる Lean の構文糖衣の1つである `⟨a,b,c⟩` 記法を単一コンストラクタ型のショートハンドとして再現します：
-/

--#--
-- slightly different notation so no ambiguity happens
--#--
-- オリジナルと紛らわしくならないようにちょっとだけ変えている
syntax (name := myanon) "⟨⟨" term,* "⟩⟩" : term

def getCtors (typ : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? typ with
  | some (ConstantInfo.inductInfo val) =>
    pure val.ctors
  | _ => pure []

@[term_elab myanon]
def myanonImpl : TermElab := fun stx typ? => do
  --#--
  -- Attempt to postpone execution if the type is not known or is a metavariable.
  -- Metavariables are used by things like the function elaborator to fill
  -- out the values of implicit parameters when they haven't gained enough
  -- information to figure them out yet.
  -- Term elaborators can only postpone execution once, so the elaborator
  -- doesn't end up in an infinite loop. Hence, we only try to postpone it,
  -- otherwise we may cause an error.
  --#--
  -- 型がわからないメタ変数である場合、実行を延期しようとする。
  -- メタ変数は関数のエラボレータのように、それらが何であるか解明するための情報が
  -- まだ十分手に入れられない際に暗黙のパラメータの値を埋めるために用いられる。
  -- 項エラボレータが実行を延期できるのは一度だけであるため、エラボレータが無限ループに陥ることはない。
  -- 従って、ここでは実行の延期だけを試みるが、そうしないと例外を引き起こすかもしれない。
  tryPostponeIfNoneOrMVar typ?
  --#--
  -- If we haven't found the type after postponing just error
  --#--
  -- もし延期しても型が見つからなかった場合はエラーとなる。
  let some typ := typ? | throwError "expected type must be known"
  if typ.isMVar then
    throwError "expected type must be known"
  let Expr.const base .. := typ.getAppFn | throwError s!"type is not of the expected form: {typ}"
  let [ctor] ← getCtors base | throwError "type doesn't have exactly one constructor"
  let args := TSyntaxArray.mk stx[1].getSepArgs
  let stx ← `($(mkIdent ctor) $args*) -- syntax quotations
  elabTerm stx typ -- call term elaboration recursively

#check (⟨⟨1, sorry⟩⟩ : Fin 12) -- { val := 1, isLt := (_ : 1 < 12) } : Fin 12
#check_failure ⟨⟨1, sorry⟩⟩ -- expected type must be known
#check_failure (⟨⟨0⟩⟩ : Nat) -- type doesn't have exactly one constructor
#check_failure (⟨⟨⟩⟩ : Nat → Nat) -- type is not of the expected form: Nat -> Nat

/-!
--#--
As a final note, we can shorten the postponing act by using an additional
syntax sugar of the `elab` syntax instead:
--#--
最後の注釈として、`elab` 構文の糖衣構文を代わりに使うことで、延期の動作を短くすることができます：
-/

--#--
-- This `t` syntax will effectively perform the first two lines of `myanonImpl`
--#--
-- この `t` 構文は `myanonImpl` の最初の2行を効果的に実行する。
elab "⟨⟨" args:term,* "⟩⟩" : term <= t => do
  sorry


/-!

--#--
## Exercises

--#--
## 演習問題

--#--
1. Consider the following code. Rewrite `syntax` + `@[term_elab hi]... : TermElab` combination using just `elab`.

--#--
1. 以下のコードについて考えてみましょう。`syntax` + `@[term_elab hi]... : TermElab` の組み合わせの代わりに `elab` だけを使って書き換えてください。

    ```lean
    syntax (name := hi) term " ♥ " " ♥ "? " ♥ "? : term

    @[term_elab hi]
    def heartElab : TermElab := fun stx tp =>
      match stx with
        | `($l:term ♥) => do
          let nExpr ← elabTermEnsuringType l (mkConst `Nat)
          return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 1)
        | `($l:term ♥♥) => do
          let nExpr ← elabTermEnsuringType l (mkConst `Nat)
          return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 2)
        | `($l:term ♥♥♥) => do
          let nExpr ← elabTermEnsuringType l (mkConst `Nat)
          return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 3)
        | _ =>
          throwUnsupportedSyntax
    ```

--#--
2. Here is some syntax taken from a real mathlib command `alias`.

--#--
2. 以下は実際の mathlib のコマンド `alias` から抜粋した構文です。

    ```
    syntax (name := our_alias) (docComment)? "our_alias " ident " ← " ident* : command
    ```

--#--
    We want `alias hi ← hello yes` to print out the identifiers after `←` - that is, "hello" and "yes".

--#--
    これについて `alias hi ← hello yes` で `←` の牛との識別子、つまり「hello」と「yes」を出力するようにしたいです。

--#--
    Please add these semantics:

--#--
    これらのセマンティクスを追加してください：

--#--
    **a)** using `syntax` + `@[command_elab alias] def elabOurAlias : CommandElab`.
    **b)** using `syntax` + `elab_rules`.
    **c)** using `elab`.

--#--
    **a)** `syntax` + `@[command_elab alias] def elabOurAlias : CommandElab` を使用する
    **b)** `syntax` + `elab_rules` を使用する
    **c)** `elab` を使用する

--#--
3. Here is some syntax taken from a real mathlib tactic `nth_rewrite`.

--#--
3. 以下は実際の mathlib の `nth_rewrite` から抜粋した構文です。

    ```lean
    open Parser.Tactic
    syntax (name := nthRewriteSeq) "nth_rewrite " (config)? num rwRuleSeq (ppSpace location)? : tactic
    ```

--#--
    We want `nth_rewrite 5 [←add_zero a] at h` to print out `"rewrite location!"` if the user provided location, and `"rewrite target!"` if the user didn't provide location.

--#--
    これについて `nth_rewrite 5 [←add_zero a] at h` でユーザが場所を指定した場合は `"rewrite location!"` を、場所を指定しなかった場合は `"rewrite target!"` を出力するようにしたいです。

--#--
    Please add these semantics:

--#--
    これらのセマンティクスを追加してください：

--#--
    **a)** using `syntax` + `@[tactic nthRewrite] def elabNthRewrite : Lean.Elab.Tactic.Tactic`.
    **b)** using `syntax` + `elab_rules`.
    **c)** using `elab`.

--#--
    **a)** `syntax` + `@[command_elab alias] def elabOurAlias : CommandElab` を使用する
    **b)** `syntax` + `elab_rules` を使用する
    **c)** `elab` を使用する

-/
