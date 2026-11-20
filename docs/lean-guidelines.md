# Lean 4 コーディング規約

このリポジトリで Lean 4 を書くときの規約。設計の背景は [design.md](design.md) を参照。

- 本文中の **[確認済]** は、2026-11-20 にローカルの Lean v4.36.0 で動作を確かめた項目である。
- それ以外は、公式ドキュメント・リリースノート・Mathlib のガイドラインの調査に基づく。

## 1. ツールチェーン

- `lean-toolchain` には `leanprover/lean4:v4.36.0` を書く。これは 2026-11-16 公開の最新 stable で、ローカルの elan 既定と一致する。
  - 2026-11-18 に v4.37.0-rc1 が出ている。rc は使わない。
- 更新の方針:
  - stable が出たら、専用の PR で上げる。
  - リリースノートの破壊的変更を確認する。
  - 依存（Plausible など）にも、同じ版のタグがあることを確認する。
- **Mathlib は使わない**（design.md §12 Q3 で決定）。理由:
  - 1 ファイルあたりの読み込みが重くなる。2026-11-20 に 1 ファイルを単体で処理して測った結果は次のとおり。Mathlib は Lean 本体と同等以上の規模である。

    | import するもの | 時間 | メモリ |
    |---|---|---|
    | なし（Init のみ） | 1.2 秒 | 385 MB |
    | `Std` | 2.1 秒 | 609 MB |
    | `Lean`（Lean 本体） | 6.3 秒 | 1.3 GB |

  - 依存の取得に、数 GB のビルド済みキャッシュ（`lake exe cache get`）が必要になる。
  - Lean の版を Mathlib の対応に合わせる必要が生じる。更新のたびに、補題の改名や `simp` の正規形の変化で証明が壊れうる。
  - 古典論理と、実行できない（noncomputable な）定義が多く、エンジンの定義では使いにくい。
- core（v4.36.0）には、`List.Perm` の補題、`omega` / `lia`、`grind`、`simp`、`decide`、`Std.HashMap` / `Std.TreeMap` の補題がある。M1〜M5 の証明はこれで足りる見込み。
- それでも `Finset` / `Multiset` での推論や `aesop` が必要になったら、**証明専用の別パッケージ**（例: `proofs/` に別の lakefile を置き、このパッケージを参照する）でだけ Mathlib を使う案を検討する。エンジンとカードのビルドには影響させない。

## 2. Lake の設定

`lakefile.toml` を使う。Lake script が要るときだけ `lakefile.lean` にする。`lake-manifest.json` はコミットする。

```toml
name = "riftbound"
version = "0.1.0"
defaultTargets = ["Riftbound"]
testDriver = "RiftboundTest"

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false
linter.missingDocs = true

[[require]]
name = "plausible"
scope = "leanprover-community"
rev = "v4.36.0"

[[lean_lib]]
name = "Riftbound"          # 検証コア（P8 の禁止事項と axiom 監査の対象）

[[lean_lib]]
name = "RiftboundCards"     # カード定義と具体的な CardDB

[[lean_lib]]
name = "RiftboundDriver"    # 乱数の供給・自動対戦・ログ再生（IO を使う。監査の対象外）

[[lean_lib]]
name = "RiftboundTest"
```

ライブラリの役割は [design.md §4](design.md#4-全体構成) を参照。

[確認済] 次の点は、上と同じ形の設定で動くことを確かめた。
- `[leanOptions]` の dotted key
- lib を `testDriver` にした `lake test`
- Plausible v4.36.0 の取得とビルド

設定の意図:
- `defaultTargets` は `Riftbound`（検証コア）だけにする。axiom の監査（§7.2）は、デフォルトのビルド対象を見るからである。全ライブラリをビルドするときは、名前を並べて指定する。
- `autoImplicit` と `relaxedAutoImplicit` は、Lean 本体の既定では `true`。綴りの誤りが、意図しない暗黙引数として受け入れられてしまうため、Mathlib と同じく `false` にする。
- `linter.missingDocs` は、公開する宣言（帰納型のコンストラクタを含む）すべてに docstring を求める。[確認済]
  - ルールの定義に CR の根拠を書かせるために有効にする（§4）。
- `lake lint` について:
  - 組み込みの環境 linter（`builtinLint = true`）は、手元の試験では "No environment linters were run" と表示された。
  - M0 で `lake lint --builtin-only` などを試し、設定を確定する。

## 3. module system

- **すべてのファイルを `module` にする。**
  - module system は v4.27.0 で experimental を外れた。
  - Mathlib の style guide も全ファイルを module にするよう求めている。
  - `lake new` のテンプレートは `module` を付けないので、自分で付ける。
- **ルールとコアのファイルは `@[expose] public section` で始める。**
  - [確認済] `@[expose]` が無いと、定義の本体が他のモジュールに公開されず、下流で `decide` や `simp` による展開ができない。
  - 同様に、`public section` の外にある定理は他のモジュールから見えない。

```lean
module

public import Riftbound.State.GameState

/-!
# Cleanup

Cleanup の 10 ステップ（CR 318-324）。
-/

@[expose] public section

namespace Riftbound
-- ...
end Riftbound

end
```

- テストのモジュールは、同じパッケージ内なので `import all Riftbound.X` で非公開部分まで読める。
- [確認済] `import Std.Data.HashMap` と `import Plausible` は、module の中から使える。
- 注意: lean-beam の文書には、module 用に `-Dexperimental.module=true` が要るという古い記述がある。M0 で lean-beam と併用できるかを確認する。

## 4. 命名・ファイル・docstring

### 4.1 命名（Lean core と Mathlib の規約に従う）

| 対象 | 規則 | 例 |
|---|---|---|
| 型・structure・inductive・型クラス | UpperCamelCase | `GameState`、`Effect`、`CardDef` |
| `Prop` を返す述語 | UpperCamelCase | `WF`、`DeckValid`、`Reachable` |
| 関数・データ | lowerCamelCase | `moveObj`、`legalActions`、`burnOut` |
| 定理 | snake_case | `moveObj_preserves_wf`、`chain_lifo` |
| 仮定の並び | `_of_` で、仮定を出現順に並べる | `wf_step_of_wf` |
| 同値 | `_iff` を付ける | `deckValid_iff` |
| `Option` を返す / panic しうる関数 | 末尾に `?` / `!` | `findObj?` |

- **語彙は CR の英語の用語に合わせる**（`conquer`、`hold`、`standardMove`、`recall`、`burnOut`）。日本語やローマ字の識別子は使わない。
- **型に属する操作は、型と同名の namespace に置き、dot notation が使えるようにする**（例: `GameState.moveObj` なら `s.moveObj`）。
  - エンジンの入口（`step`、`legalActions`、`view`）のように特定の型に属さないものは、`Riftbound.Engine` などの機能の namespace に置く。設計文書で素の名前（`step`、`moveObj`）を使っているのは略記である。
- **カード定義の名前**:
  - 弾の namespace の下に、名前と subtitle を lowerCamelCase にしたものを置く（例: `RiftboundCards.Origins.fallingStar`、`RiftboundCards.Origins.ahriAlluring`）。
  - 生成ブロックのメタデータは `<名前>.meta` とする（例: `fallingStar.meta`）。
  - 一意性は生成スクリプトが保証する。

### 4.2 ファイル

- ファイル名は UpperCamelCase で、モジュール名と対応させる（`Riftbound/Rules/Combat.lean` は `Riftbound.Rules.Combat`）。
- 1 ファイルは目安として 1,000 行以内にする。Mathlib の linter が警告する上限は 1,500 行。
  - **例外**: カードの定義（`RiftboundCards/<Set>.lean`）は 1 弾 1 ファイルとし、この上限を適用しない（design.md §12 Q1、card-data.md §4.1）。
- 行長は 100 文字以内。インデントは 2 スペースで、複数行にわたる宣言ヘッダの続きは 4 スペース。
- `by` は行末に置く。`fun x ↦ ...` を使い、`λ` は使わない。

### 4.3 docstring と規則番号

- 各ファイルの先頭に、module docstring（`/-! # 題名 ... -/`）を書く。
- 公開する宣言には、docstring（`/-- ... -/`）を書く（`linter.missingDocs` が強制する）。
- **ルールに由来する定義には、規則番号を `(CR 323.4)` の形で書く。** Tournament Rules は `(TR 402.1)` と書く。複数あるときは `(CR 323.4, 142.4.b)`。
  - この形式を崩さないこと。スクリプトで抽出して、規則のカバレッジ表や改番時の置換に使う（design.md §9）。
- docstring は英語を基本とする。CR の用語をそのまま使えるからである。`docs/` の設計文書は日本語で書く。
- カードの定義の docstring には、公式の英語の文面をそのまま入れる（card-data.md §4.1）。
- Verso 形式の docstring（`doc.verso`）は、まだ experimental なので使わない。

## 5. 証明しやすいコードの書き方

### 5.1 再帰と停止性

- **`Riftbound` ライブラリでは `partial` と `unsafe` を使わない。**
  - `partial` な定義は kernel にとって不透明で、展開も簡約もできず、証明できない。
  - `RiftboundDriver` と `Main`（対局ループや IO）では使ってよい。これらは証明の対象外で、`Riftbound` から import しない。
- 構造再帰を優先する。意図を明示するときは `termination_by structural x` と書く。
- 測度を見つけにくい自動処理（Cleanup の反復、効果の解決など）は、**再帰しない 1 歩の関数 `microStep` と、それを `fuel : Nat` の回数だけ繰り返す構造再帰 `advance`** に分ける（design.md §6.1）。
  - fuel が尽きたらエラーを返す。
  - fuel の単調性（ある fuel で成功するなら、それ以上の fuel でも同じ結果になる）は、`advance` を作るのと同時に証明する（roadmap.md の I15）。
  - 性質の証明は、`microStep` の場合分けと、fuel についての帰納法に分かれる。
- **[確認済] 効果の解釈器は、`Effect` の構造再帰では書けない。** `custom` の展開のように、解釈の途中で別の `Effect` を実行する箇所があると、v4.36.0 は停止性を示せない（"failed to infer structural recursion"）。これが 1 歩の関数にする理由の 1 つである。
- 上限が内側で決まる反復（Layers の反復など）は、その上限を回数にした構造再帰にし、fuel を外から受け取らない（design.md §5.4）。
- 整礎再帰（`termination_by` で測度を与えるもの）は、定義上は簡約されにくい。`decide` で評価したい関数には使わない。

### 5.2 状態と不変条件

- 状態は素直な `structure` / `inductive` にし、不変条件は別の述語で持つ。Subtype に埋め込むのは `Fin n` などの局所的なものだけにする。
- 不変条件は 2 つに分ける（design.md §5.2）。
  - `WF`: 構造の条件。どの中間状態でも成り立つ。
  - `Settled`: Cleanup の不動点で成り立つ条件。規則の上で一時的に破れるものは、こちらに入れる。
- `WF` と `Settled` には `Decidable` のインスタンスを用意し、テストで実行時の自己検査に使えるようにする。
- 状態の型（`GameState` と、その部品）は `deriving DecidableEq, Repr` が通る形に保つ。巻き戻しの一致や冪等性を `=` で述べ、小さな例を `decide` で検査するためである（§5.3）。
- 導出できる値は状態に持たない（例: Open / Closed は Chain から導出する）。

### 5.3 データ構造

- **まず `List` で書く。** 証明の補題が最も揃っている。
  - プロファイルで遅いと分かった箇所だけ `Array` に替える。証明の上では、`Array` は `List` を包んだものとして扱える。
- **検証コアの状態に入れる写像は、`Std.ExtTreeMap` にする。** 外延的な等しさを持つ写像で、内容が同じなら `=` になる。
  - [確認済] `Std.ExtTreeMap` をフィールドに持つ structure は、`deriving DecidableEq, Repr` が通る。
  - [確認済] `decide` で、検索（`(∅.insert 1 2)[1]? = some 2`）、挿入して削除すると元に戻ること、挿入の順序によらない等しさ、Exhaust を 2 回行っても 1 回と同じ状態になること、が閉じる。
  - [確認済] `(m.insert k v)[k]? = some v` のような基本補題は、`simp` で閉じる。`toList` と `keys` は、挿入の順序によらず鍵の順に並ぶ。`foldl` も使える。
  - [確認済] `Std.TreeMap` をフィールドに持つ structure は、`deriving DecidableEq` が失敗する（`Decidable (a = b)` を合成できない）。
  - [確認済] `Std.HashMap` の検索は、`decide` で評価できない（kernel の簡約が途中で止まる）。
  - `Std.TreeMap` と `Std.HashMap` の `==` は内容を比べるが、`=` は内部の形まで比べる。状態の等しさを定理で述べるには向かない。
- `Std.HashMap` は、`RiftboundDriver` とテストの補助でだけ使う。結果が hash の順序に依存する処理は書かない。
- `Lean.RBMap` は v4.32.0 で deprecated になった。
- 固定長のものは `Vector α n` や `Fin n` を使う。

### 5.4 `deriving` と等値性

- 小さな列挙型やレコードは `deriving DecidableEq, Repr, Hashable` にする。`BEq` は `DecidableEq` から自動で得られ、lawful になる。
  - **同じ型に `BEq` を別途 derive しない。** 2 つの `BEq` が併存すると、`==` がどちらを使うかがインスタンスの優先順位で決まってしまう。
- **[確認済] 入れ子の帰納型（`List Effect` をフィールドに持つ `Effect` など）では、v4.36.0 の `deriving DecidableEq` と `deriving ReflBEq, LawfulBEq` は失敗する。** `Repr`、`BEq`、`Hashable` の derive は通る。効果 IR では、次のどれかを選ぶ。
  1. 入れ子のまま `deriving Repr, BEq, Hashable` にし、`DecidableEq` は相互再帰で手書きする。書き味が良いので、これを推奨する。
  2. `List` の代わりに専用のリスト型を `mutual` で定義する。`deriving DecidableEq` が通る。
  3. 等値性が要らない型なら、`Repr` と `BEq` だけにする。
- **[確認済] 入れ子の帰納型には、v4.36.0 の `induction` タクティクが使えない**（"does not support ... nested inductive type" というエラーになる）。
  - 代わりに、関数と同じ形の相互再帰で定理を書く（`mutual` の中で `theorem` をパターンマッチで定義する）。こちらは通ることを確認した。
  - この書き方が要るのは、`Effect` を静的に走査する関数（等値性、変数の束縛の検査、対象枠の検査）についての定理である。
  - 解釈器は 1 歩の関数にするので（§5.1）、`WF` の保存（design.md §8 の L4）は場合分けで示せ、`Effect` についての帰納法は要らない。
- **カードを巨大な列挙型のコンストラクタにしない。**
  - derive される `ReflBEq` / `LawfulBEq` の証明はコンストラクタ数の二乗で重くなる。
  - v4.35 では `deriving DecidableEq` が遅くなったという報告もある。
  - カードはデータとして持つ（design.md §7）。
- HOAS（Lean の関数をフィールドに持つ帰納型）は使わない。`DecidableEq` も `Repr` も導出できず、カードデータを解析することもできないためである。

### 5.5 Decidable と `decide`

- v4.35.0 で `Decidable` は、inductive から「`Bool` と、その反映の証明」を持つ structure に変わった。
  - 新しいインスタンスは `decidable_of_iff` か `decidable_of_bool` で作る。
- 検証のコアでは **`native_decide` を使わない**。コンパイラ全体を信頼の対象に加えることになるからである。
  - 大きな計算の検査は、`#guard` か `#eval` によるテストで行う。
- `decide` で展開する定義は、モジュールをまたぐ場合 `@[expose]` が必要になる（§3）。
- 数百件のカード定義に対する整形性の検査（`CardDB.WF`）は、kernel で評価する `decide` では重すぎる可能性がある。M0 のスパイクで測り、重ければコンパイル実行の `#guard` で検査する。

### 5.6 タクティク

- **`simp` 補題**:
  - 左辺より右辺が単純な向きにする。
  - 可換律に `@[simp]` を付けない。
  - 重複する補題を作らない。
  - 補題が足りないと感じたら、`rfl` で押し切らずに補題を足す。
- **`grind`**:
  - core の標準ライブラリにも注釈が付いている。積極的に使ってよい。
  - `@[grind]` 属性は、常に使ってほしい補題に限って控えめに付ける。
- **算術**: `omega` か、その対応物の `lia` を使う。
- **`vcgen`**（`Std.Do` の後継）は v4.36.0 ではまだ experimental で、使うたびに警告が出る。コアの証明は依存させない。
- `erw` は使わない。
- `set_option maxHeartbeats` は宣言単位（`in`）でだけ上げる。上げる前に原因を潰す。

### 5.7 モナドと純粋性

- ルールの関数は純粋な `Except RuleError α` か、状態を明示的に受け渡す関数にする。transformer は重ねない。
- `IO` は Driver と CLI（`Main.lean`）に閉じ込める。

## 6. テスト

| 手段 | 用途 |
|---|---|
| `#guard e` | 定義の直後や、テストのモジュールに置く小さな実行検査 |
| `#guard_msgs in ...` | 出力やエラーメッセージの固定 |
| `example : p := by decide` | kernel で評価できる性質の検査 |
| `RiftboundTest`（`lake test` の test driver） | シナリオテスト、公式 FAQ の回帰、性質ベーステスト |
| Plausible | `Arbitrary` を derive して、ランダムな合法手の列の後でも `WF` が成り立つことを検査する（証明の前の早期発見） |

- **シナリオテスト**は、「状態を組み立てる → Action の列を流す → 結果を検査する」の形に揃える。そのための小さな DSL を `RiftboundTest/Scenario` に用意する。
  - 解釈器が指示を飛ばしたときの診断用のイベント（design.md §7.1）が発行されていないことを、DSL の側で常に検査する。
- **列挙の照合テスト**: 小さな状態で、`legalActions` の結果を、「候補を作って `step` で試し、通ったものを残す」方法の結果と比べる（design.md §11）。この方法を `legalActions` の定義に使うことは禁止している。
- テストでは `native_decide` を使ってもよい。ただし `Riftbound` ライブラリの定理から参照しないこと。

## 7. 作業の単位とローカルでの検証

開発者が 1 人の間は、検証をすべてローカルで行う。GitHub Actions は使わない（design.md §12 Q7）。

Lean では、ビルドが通ることが「証明が kernel の検査を通った」ことを意味する。だから小さな単位で書き、単位ごとにビルドを通してから先へ進む。

### 7.1 作業の単位

- **1 単位は、1 つの定義か、1 つの定理とする。** 切り離せないもの（相互再帰の定義、定義とその `Decidable` のインスタンスなど）は、まとめて 1 単位にしてよい。
- 単位ごとに、次の順に進める。
  1. 定義か、定理の主張を書く。
  2. 定理なら証明を書く。定義なら、直後に `#guard` か `example` で小さな検査を書く（§6）。
  3. そのモジュールをビルドする（§7.2）。エラーも警告も無いことを確かめる。
  4. 通ってから、次の単位に進む。
- **証明が通っていない定理の上に、次の単位を積まない。**
  - 書いている途中で `sorry` を置くのはよい。ただし、`sorry` を残したまま次の単位に進まず、コミットもしない。
  - 証明に行き詰まったら、先へ進まずに、主張か定義を見直す。
  - 後回しにする定理は、コードに残さない。メモか Issue に書く。
- 定理は、それを使う側より先に書く。下の層から積む順序（roadmap.md）が、そのまま単位の順序になる。
- **コミットは、1 単位か、密接に関連する数単位ごとに行う**（例: 1 つの定義と、その補題）。
  - どのコミットも、`--wfail` を付けた全体のビルドが通る状態にする。
  - コミットメッセージに、足した定義と定理の名前を書く。
- **PR は、1 つのまとまりごとに作る**（1 つのファイル、1 つの手続きなど）。マイルストーンをまるごと 1 つの PR にしない。
- エージェントが実装する場合も、同じ単位で進める。
  - 単位ごとに、ビルドの結果を自分で確かめる。
  - 報告には、足した定理の名前と、実行した検証コマンドとその結果を書く。
  - lean-beam（§8）で試した結果は、確認の代わりにしない。最後は必ず `lake build` で確かめる。

### 7.2 検証のコマンド

| いつ | コマンド | 確かめること |
|---|---|---|
| 単位ごと | `lake build Riftbound.Rules.Move --wfail`（書いているモジュールを指定する） | その定義と定理が検査を通る。警告と `sorry` が無い |
| コミットの前 | `lake build Riftbound RiftboundCards RiftboundDriver RiftboundTest --wfail` と `lake test` | 全体が通る。下流のモジュールを壊していない |
| main へのマージの前 | `scripts/verify.sh`（全体の検証） | 下の一覧のすべて |

`scripts/verify.sh` は、次を順に実行する。1 つでも失敗したら、そこで止まる。

1. 全ライブラリのビルド（`--wfail`）
2. `lake test`
3. axiom の監査（`lake check --inadvisably-no-sandbox`）
4. カードデータの陳腐化検査（`uv run scripts/gen_lean.py --check`。[card-data.md](card-data.md)）
5. CR の引用の抽出と、カバレッジ表の生成

- **`--wfail`** は警告をエラーにする。
  - [確認済] `sorry` を含むモジュールは、`--wfail` を付けるとビルドが失敗する（"declaration uses `sorry`" の警告がエラーになる）。付けないと、警告が出るだけでビルドは成功する。
  - [確認済] モジュール名を指定したビルド（`lake build Chk.Basic --wfail`）は、そのモジュールと依存先だけをビルドする。
- **axiom の監査**には `lake check` を使う（v4.35.0 で追加）。デフォルトのビルド対象を kernel で再生し、`propext`、`Classical.choice`、`Quot.sound` 以外の axiom を使う宣言があると失敗する。
  - [確認済] `lake check` は、対象のコードを bubblewrap のサンドボックスの中でビルドする。macOS ではサンドボックスが使えず、そのままではエラーになる。
  - [確認済] macOS では、`--inadvisably-no-sandbox` を付けると動く。サンドボックスは、信頼できないコードを検査するときの備えである。自分で書いたコードを自分のマシンで検査するので、無くても差し支えない。
  - [確認済] この形で、自分で宣言した `axiom` を使う定理と、`native_decide` を使う定理が、どちらも拒否される。
  - 監査の対象は `Riftbound` ライブラリだけにする。`lake check` はデフォルトのビルド対象を見るので、`defaultTargets` を `["Riftbound"]` にしておけばよい（§2）。`RiftboundDriver` とテストは対象外。
- **マージの前に、`scripts/verify.sh` の結果を PR の説明に書く。** CI が無いので、これが検証を通した記録になる。
- 開発者が増えたら、同じ `scripts/verify.sh` を GitHub Actions で実行する（`leanprover/lean-action`）。そのときは Linux なので、`lake check` をサンドボックスつきで使える。

## 8. 開発支援ツール

- **lean-beam**:
  - v4.36.0 の toolchain に同梱されている、Lean FRO の CLI と MCP サーバ。
  - 編集せずにタクティクを試す、`sorry` を探す、ゴールを見る、といった操作ができる。
  - 登録には toolchain 内の絶対パスを使う。

  ```bash
  claude mcp add --scope user lean-beam -- \
    "$HOME/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean-beam-mcp"
  ```

  - beta 版である。読むのは保存済みのファイルなので、最後は必ずクリーンな `lake build` で確認する。
- **lean-lsp-mcp**（`uvx lean-lsp-mcp`）: LSP を MCP 経由で使う。検索系の機能は Mathlib 向けなので、このプロジェクトでは lean-beam を主に使う。

## 9. 参考資料

- Lean Language Reference: https://lean-lang.org/doc/reference/latest/
  - リリースノート: https://lean-lang.org/doc/reference/latest/releases/
- Lean core の命名・スタイル:
  - https://github.com/leanprover/lean4/blob/master/doc/std/naming.md
  - https://github.com/leanprover/lean4/blob/master/doc/std/style.md
- Mathlib の命名・スタイル・ドキュメント:
  - https://mathlib.org/contribute/naming.html
  - https://mathlib.org/contribute/style.html
  - https://mathlib.org/contribute/doc.html
- Functional Programming in Lean: https://lean-lang.org/functional_programming_in_lean/
- Theorem Proving in Lean 4: https://lean-lang.org/theorem_proving_in_lean4/
- lean-action: https://github.com/leanprover/lean-action
- Plausible: https://github.com/leanprover-community/plausible
- lean-beam: https://github.com/ejgallego/lean-beam
