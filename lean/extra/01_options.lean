/-
--#--
# Extra: Options
--#--
# 付録：オプション
--#--
Options are a way to communicate some special configuration to both
your meta programs and the Lean compiler itself. Basically it's just
a [`KVMap`](https://github.com/leanprover/lean4/blob/master/src/Lean/Data/KVMap.lean)
which is a simple map from `Name` to a `Lean.DataValue`. Right now there
are 6 kinds of data values:
--#--
オプションはメタプログラムと Lean のコンパイラの両方に特別な設定を伝える機能です。基本的にこれは [`KVMap`](https://github.com/leanprover/lean4/blob/master/src/Lean/Data/KVMap.lean) であり、`Name` から `Lean.DataValue` への単純なマップです。現在、6種類のデータ値を有します：

- `String`
- `Bool`
- `Name`
- `Nat`
- `Int`
- `Syntax`

--#--
Setting an option to tell the Lean compiler to do something different
with your program is quite simple with the `set_option` command:
--#--
`set_option` コマンドを使うことで、とても簡単に Lean コンパイラにプログラムに対して何か違うことを行うように指示するオプションを設定することができます：
-/

import Lean
open Lean

#check 1 + 1 -- 1 + 1 : Nat

set_option pp.explicit true -- No custom syntax in pretty printing

#check 1 + 1 -- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 1 1 : Nat

set_option pp.explicit false

/-!
--#--
You can furthermore limit an option value to just the next command or term:
--#--
さらに、オプションの値をすぐ次のコマンドや項だけに限定することもできます：
-/

set_option pp.explicit true in
#check 1 + 1 -- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 1 1 : Nat

#check 1 + 1 -- 1 + 1 : Nat

#check set_option trace.Meta.synthInstance true in 1 + 1 -- the trace of the type class synthesis for `OfNat` and `HAdd`

/-!
--#--
If you want to know which options are available out of the Box right now
you can simply write out the `set_option` command and move your cursor
to where the name is written, it should give you a list of them as auto
completion suggestions. The most useful group of options when you are
debugging some meta thing is the `trace.` one.

--#--
もし今すぐ利用可能なオプションを取り出したい場合は、`set_option` コマンドを実行し、カーソルをその名前が書かれている場所に移動するだけで、自動補完の候補としてそれらのオプションのリストが表示されるでしょう。メタ関連でデバッグをしているときに最も役に立つオプションは `trace.` から始まるものです。

--#--
## Options in meta programming
--#--
## メタプログラミングにおけるオプション
--#--
Now that we know how to set options, let's take a look at how a meta program
can get access to them. The most common way to do this is via the `MonadOptions`
type class, an extension to `Monad` that provides a function `getOptions : m Options`.
As of now, it is implemented by:
--#--
これでオプションを設定する方法がわかったので、メタプログラムがオプションにアクセスする方法を見てみましょう。最も一般的な方法は `MonadOptions` 型クラスを通じたもので、これは `Monad` に関数 `getOptions : m Options` を拡張したものです。現時点でこれは以下に対して実装されています：

- `CoreM`
- `CommandElabM`
- `LevelElabM`
--#--
- all monads to which you can lift operations of one of the above (e.g. `MetaM` from `CoreM`)

--#--
- 上記のいずれかの操作を持ち上げることができるすべてのモナド（例えば、`CoreM` から `MetaM`）

--#--
Once we have an `Options` object, we can query the information via `Options.get`.
To show this, let's write a command that prints the value of `pp.explicit`.
--#--
一度 `Options` オブジェクトを取得すれば、`Options.get` を使って情報を照会することができます。これを示すために、`pp.explicit` の値を表示するコマンドを書いてみましょう。
-/
elab "#getPPExplicit" : command => do
  let opts ← getOptions
  -- defValue = default value
  logInfo s!"pp.explicit : {opts.get pp.explicit.name pp.explicit.defValue}"

#getPPExplicit -- pp.explicit : false

set_option pp.explicit true in
#getPPExplicit -- pp.explicit : true

/-!
--#--
Note that the real implementation of getting `pp.explicit`, `Lean.getPPExplicit`,
uses whether `pp.all` is set as a default value instead.

--#--
`pp.explicit` を取得するた実際の実装である `Lean.getPPExplicit` は代わりに `pp.all` がデフォルト値として設定されているかどうかを使用することに注意してください。

--#--
## Making our own
--#--
## 独自のオプションを作る
--#--
Declaring our own option is quite easy as well. The Lean compiler provides
a macro `register_option` for this. Let's see it in action:
--#--
独自のオプションを宣言するのも非常に簡単です。Lean コンパイラはこのために `register_option` というマクロを用意しています。実際に使ってみましょう：
-/

register_option book.myGreeting : String := {
  defValue := "Hello World"
  group := "pp"
  descr := "just a friendly greeting"
}

/-!
--#--
However, we cannot just use an option that we just declared in the same file
it was declared in because of initialization restrictions.
--#--
しかし、初期化の制約があるため、宣言したオプションをそのまま同じファイルで使うことはできません。
-/
