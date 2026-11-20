# Riftbound Lean4 実装方針

本書は、要求の正本である [`docs/original.md`](original.md) を前提にした実装方針である。`original.md` は人間だけが編集する。本書と食い違う場合は `original.md` を優先する。

関連文書:

- [rules-model.md](rules-model.md) — Riftbound Core Rules を形式化の観点で整理したもの（規則番号つき）
  - 本書で定義なしに使うルール用語（Chain、Pending / Finalize、HOT FEPR、Cleanup、Contested、Staged、Showdown、Mighty など）は、こちらを参照。
- [lean-guidelines.md](lean-guidelines.md) — このリポジトリの Lean 4 コーディング規約
- [card-data.md](card-data.md) — カードデータの取り込みと、効果 IR への落とし込み
- [roadmap.md](roadmap.md) — マイルストーンと、証明を積み上げる順序

---

## 1. 要求の整理

`original.md` の要求を次の 5 つに分ける。

| ID | 要求（original.md） | 設計上の解釈 |
|---|---|---|
| R1 | Lean4 で実装する | 実行できるルールエンジンと、その性質の証明を、同じ Lean コードベースに置く |
| R2 | ルールは公式のルールに則る | 各定義から Core Rules の規則番号を辿れるようにする。合法性は、CR から直接書いた仕様 `Legal` として独立に持つ。ルール改訂に追従する手順を持つ |
| R3 | 新カードの追加時にその効果を反映できる | カードは「データ + 効果 IR（中間表現）」で表す。エンジンはカードの集合（`CardDB`）を引数に取り、定理はすべての `CardDB` について述べる。新カードの追加は、原則としてデータの追加で済ませる |
| R4 | 小さいところから証明を積み上げる | ゾーン移動などのプリミティブで一度だけ証明し、手続き・大域不変条件・カードへと積み上げる |
| R5 | 全カードをコード化し、カードでできること全てができる | エンジンはプレイヤーの選択肢を勝手に狭めない。すべての選択を決定要求として外に出し、合法手を漏れなく列挙する |

R5 の「できること全て」は、本書では次の 2 点の両立と定義する。

1. **表現の完全性**: 全カードの効果がモデル上に存在する（[roadmap.md](roadmap.md) の最終マイルストーンで判定する）。
2. **選択の完全性**: CR 上プレイヤーに許される選択は、すべて合法手として現れる。
   - 実装（`step`、`legalActions`）と独立に書いた仕様 `Legal` に対して、一致を定理で示す（§6.3）。
   - `step` と `legalActions` の間の整合だけでは、両方が同じ手を落としていても成り立ってしまう。だから独立した仕様が要る。

## 2. 前提とするバージョン

| 対象 | 版 | 備考 |
|---|---|---|
| ルール | **Riftbound Core Rules, Last Updated 2026-10-09**（Radiance 版、2026-10-16 発効） | 以下「CR」と略す。規則番号はすべてこの版のもの |
| カードプール | Origins, Proving Grounds, Spiritforged, Unleashed, Vendetta, Radiance | 2026-11-20 時点。公式ギャラリー上で 1,416 件の印刷、論理カードは約 1,100 種 |
| Lean | `leanprover/lean4:v4.36.0` | 2026-11-16 公開の最新 stable。ローカルの elan 既定と一致 |

近い将来の変化:

- **2027-01-29 発売の Legacy で、Core Rules の書式が全面的に刷新されると予告されている。** メカニクスは変えないとされるが、規則番号は大きく変わる見込み。
- 同時にカード文面のテンプレートも変わる。例: "When you play me" は "When I enter" に、トークンの生成は "Play" から "Create" に変わる。
- どちらも §9 の版管理で吸収する。改訂を待たずに着手してよい。

## 3. 設計原則

| # | 原則 | 理由 |
|---|---|---|
| P1 | **状態遷移は実行できる関数 `step` で定義し、合法性は CR から直接書く仕様 `Legal`（`Prop`）として独立に持つ。** 両者の一致を定理として積む。遷移そのものを関係で書く仕様は、検証したい一部（戦闘ダメージなど）にだけ足す | `#eval` で対戦を進められ、`simp` で展開できる。合法性の仕様が実装と独立していれば、R2 と R5 の根拠になる |
| P2 | **状態は素直なデータにし、不変条件は別の述語 `WF` で持つ。** 依存型で縛るのは `Fin` などの葉に限る | 失敗しうる遷移（`Except`）と相性がよい。カード追加のたびに証明を求められない |
| P3 | **エンジンはカードを知らない。** カード名で分岐せず、カードの集合 `CardDB` を引数で受け取る。ルールを曲げるカードのための差し込み口（hook）を最初から用意する | 成熟した TCG エンジン（MTG Arena の GRE、Argentum Engine）がこの形で拡張性を得ている。定理を特定のカード集合に固定しないためでもある |
| P4 | **プレイヤーの選択はすべて明示的な決定要求にする。** 状態の中に「誰が何を決める番か」を継続のスタックとして持ち、`Action` で答えを受け取る。**コアは選択を自動で決めない**（自動化は Driver の機能） | R5（選択の完全性）。直列化・再生・合法手の列挙が容易になる |
| P5 | **乱数をコアに持たない。** シャッフルなどは「偶然の決定」として外から結果を受け取り、エンジンは妥当性（置換であること）だけを検査する | `step` が決定的な全域関数のままになり、「どのシャッフル結果でも成り立つ」を量化で述べられる |
| P6 | **ゾーン移動は 1 つのプリミティブ `moveObj` に集約する** | 保存則・一意性を一度だけ証明すれば、それを使う全効果・全カードに効く |
| P7 | **規則番号を辿れるようにする。** 各定義の docstring に `(CR 323.4)` の形で根拠を書く | 公式ルールへの準拠（R2）を確認でき、改訂時の影響範囲を機械的に洗い出せる |
| P8 | **検証コアに `partial` / `unsafe` / `native_decide` / `sorry` を入れない。** CI で axiom を監査する | `partial` な定義は kernel から不透明で証明できない。`native_decide` はコンパイラを信頼対象に加えてしまう |

## 4. 全体構成

```text
 カードデータ（公式ギャラリー等）
        │  scripts/（uv + Python）: 取得・正規化・Lean 生成
        ▼
 RiftboundCards（ライブラリ）: セットごとの CardDef と、具体的な CardDB
        │ CardDB を引数として渡す（Riftbound 側は RiftboundCards を import しない）
        ▼
 Riftbound（検証コア）
   Core ─→ Card ─→ State ─→ Rules ─→ Engine
   基本型   効果IR   状態・    手続き・  step / legalActions / view
            CardDef  継続      解釈器
                              └─→ Spec（Legal: CR から直接書く合法性）
                              └─→ Invariant（WF・保存則・一致の定理）
 RiftboundDriver（ライブラリ）: 乱数の供給、自動対戦、ログ再生（IO を使う。検証の対象外）
 RiftboundTest: シナリオ・公式 FAQ の回帰・性質ベーステスト
```

矢印は import の向き（左が右に import される）。循環を避けるため、層を次の順に固定する。

1. `Core`: ID、Domain、CardType、Keyword、Cost などの基本型
2. `Card`: 効果 IR と `CardDef`、`CardDB`
3. `State`: オブジェクト、ゾーン、決定要求と継続、`GameState`、`WF`
4. `Rules`: 手続きと効果の解釈器
5. `Engine`

### 4.1 ディレクトリ構成（案）

CR の章立てとファイルを対応させ、規則から実装を引けるようにする。

```text
lean-toolchain                 -- leanprover/lean4:v4.36.0
lakefile.toml
Riftbound.lean                 -- ルート（全モジュールを import）
Riftbound/
  Basic/                       -- ルールに依存しない汎用の定義・補題（List.Perm 補助など）
  Core/
    Ids.lean                   -- PlayerId / ObjId / PhysId / CardId / Timestamp
    Domain.lean  CardType.lean  Keyword.lean  Cost.lean
  Card/
    Syntax.lean                -- Effect / Selector / Amount / Condition / Trigger / Duration / Cost式
    Ability.lean               -- Ability
    CardDef.lean               -- CardDef
    CardDB.lean                -- CardDB（カード定義と custom ハンドラの表）と、その整形性 CardDB.WF
  State/
    Object.lean                -- ゲームオブジェクト（種別: カード / トークン / Chain 上の能力）、ステータス
    Zone.lean                  -- ゾーン（105-109）と Location（197-200）
    Decision.lean              -- 決定要求と継続のフレーム
    GameState.lean
    WF.lean                    -- 不変条件
  Rules/
    Move.lean                  -- 唯一のゾーン移動プリミティブ moveObj
    Actions/*.lean             -- ゲームアクション（408-446）: Draw, Recycle, Channel, Burn Out ...
    Characteristics.lean       -- Layers による実効特性の導出（475-482）
    Interp.lean                -- 効果の解釈器（途中で中断・再開できる）
    Deck.lean                  -- デッキ構築（101-103）
    Setup.lean                 -- セットアップ（110-118）
    Turn.lean                  -- ターンとフェイズ（301-317）
    Cleanup.lean               -- Cleanup（318-324）
    Chain.lean                 -- Chain と HOT FEPR（325-340）
    Showdown.lean              -- Showdown（341-348）
    Play.lean                  -- カードのプレイ（349-359）
    Ability.lean               -- 能力（360-407）
    Movement.lean              -- 移動と Recall（447-460）
    Combat.lean                -- 戦闘（461-468）
    Scoring.lean               -- 得点と勝利（469-474, 193-196）
    Modes.lean                 -- ゲームモード（483-491）
  Engine/
    Action.lean  Step.lean  LegalActions.lean  View.lean
  Spec/
    Legal.lean                 -- 合法性の仕様（決定の種類ごとに CR から直接書く）
    Combat.lean ...            -- 遷移の関係仕様（必要な部分だけ）
  Invariant/                   -- WF 保存、一致の定理、Reachable
RiftboundCards/
  Origins/ ProvingGrounds/ Spiritforged/ Unleashed/ Vendetta/ Radiance/
  Registry.lean                -- 具体的な CardDB
RiftboundDriver/               -- 乱数の供給、自動対戦、ログ再生
RiftboundTest/
  Scenario/  Faq/  Property/
Main.lean                      -- CLI（後期）
scripts/                       -- カードデータの取得・Lean 生成・カバレッジ集計（uv 管理）
```

- `Riftbound` は検証コアで、§3 P8 の禁止事項と axiom 監査の対象になる。
- `RiftboundDriver` と `Main` は `IO` やループを使うので、監査の対象外にする。

## 5. データモデル

### 5.1 識別子

| 識別子 | 意味 | 根拠 |
|---|---|---|
| `PlayerId` | 席 | 115（手番順） |
| `PhysId` | 物理カード（デッキリストの 1 枚ずつ）。保存則はこの単位で述べる | トークンはカードではなく、PhysId を持たない（185） |
| `ObjId` | ゲームオブジェクト | **Non-Board ゾーンへ（から）移ると新しいオブジェクトになる**（124）。そのとき新しい ObjId を払い出す。Non-Board ゾーンを経由しない移動（Base と Battlefield の間の Move など）では ObjId は変わらない |
| `CardId` | 論理カード（カード定義）。トークンの定義にも CardId を振る | 印刷違い（showcase、alt-art、signature など）は同じ CardId にまとめる |
| `Timestamp` | 効果が適用され始めた時点（482） | 状態の中のカウンタ `nextTimestamp` から払い出す |

ObjId の払い出しで、次の 2 つの性質がデータ構造から直接出てくる。

- 「Non-Board ゾーンを経由して戻ったものは別オブジェクトで、対象として不正」（359.3.e）
- 一時的な修正がすべて失われること（124.1）

### 5.2 ゾーンとオブジェクト

- **ゾーンの中身は `List ObjId` で持ち、これを真実の源にする。** Main Deck・Rune Deck・Chain のように順序があるゾーンも同じ表現にする。
- CR のゾーンに加えて、エンジン内部用のゾーン **`setAside`**（プレイヤーごと）を持つ。マリガンで脇に置いたカード（117.1）などを入れる。
- **オブジェクトの表**: 属性は ObjId をキーとする表に置く。
  - 種別: カード（PhysId と CardId を持つ）、トークン（CardId を持つ）、Chain 上の能力（発生源と能力への参照を持つ）。
  - 属性: Owner、Controller、ステータス、ダメージ、カウンター、Attach 先、timestamp など。
- 不変条件 `WF` に入れるもの（初期案）:
  - 全ゾーンの列を連結したものが `Nodup` である（位置の一意性）
  - 表の定義域が、ゾーン上の ObjId の集合と一致する
  - すべての ObjId が `nextId` 未満である
  - Attach 関係が整合している（Unit は Attach されない: 143.5）
  - 各 Facedown Zone の中身が、その時点の最大容量を超えない（容量は効果で増減する: 107.3.b）
- Board と Non-Board を区別する（105-109）。
  - Base と Battlefield は Location（197-200）。Battlefield は Location であると同時にゲームオブジェクトでもある（170）。
  - Facedown Zone は Battlefield ごとの副ゾーンで、Location ではない（107.3.e）。

### 5.3 ターン状態

| 要素 | 持ち方 | 根拠 |
|---|---|---|
| Phase / Step | Awaken、Beginning（Beginning Step / Scoring Step）、Channel、Draw、Main、Ending（Ending Step / Expiration Step） | 315-317 |
| Neutral / Showdown | 進行中の Showdown / Combat を `Option` で持つ | 308 |
| Open / Closed | **保存しない。** Chain が空かどうかから導出する | 309 |
| Priority / Focus | `Option PlayerId` | 311-313 |
| 未処理タスク | HOT FEPR のタスク列（Cleanup、Start of Turn、Combat の各 Step など） | 333-334 |
| ターン単位の記録 | 今ターンに Score した（プレイヤー、Battlefield）の組。今ターンに finalize したカード（Legion 用）など | 472（Score の制限はプレイヤー単位。2v2 ではチーム単位: 491.8.b）、812 |
| プレイヤー資源 | Rune Pool（Energy、ドメイン別 Power）、XP、得点 | 166-167, 728-733, 194 |
| カウンタ | `nextId`、`nextTimestamp` | 124, 482 |

方針: 導出できるものは保存しない（冗長な状態は不変条件を増やすため）。

### 5.4 特性の導出（Layers）

- 実効特性は `characteristics : CardDB → GameState → ObjId → Characteristics` で毎回導出する。
  - 基底は CardDef の印刷値。
  - その上に 4 層を順に適用する（479）: Copy → Trait-Altering → Ability-Altering → Arithmetic。
  - **1 巡で終わりではない。** 適用によって新たに適用可能になった効果があれば、変化がなくなるまで層の評価を繰り返す。ただし各効果の適用は 1 回だけ（478.2-478.4）。実装では fuel を持たせる。
- 継続効果の扱い:
  - **Passive** は保存せず、盤面上のオブジェクトから導出する。timestamp は、そのオブジェクトの記録（Board に出た時点や、Inactive から戻った時点: 482.2）を使う。
  - **期間つき効果**（"this turn" など）は、「効果 + timestamp + 期間」のリストとして状態に保存する。失効はリストから取り除くだけで済む。
- 同一層内の依存関係（480-481）は、まず timestamp 順（482）だけで実装する。依存の判定は、それが必要なカードが来た時点で実装する（[roadmap.md](roadmap.md) M6）。

## 6. エンジンの形

### 6.1 中核 API

```lean
/-- エンジンの設定。fuel は自動処理の上限。 -/
structure EngineConfig where
  fuel : Nat

inductive RuleError where
  | illegal (reason : IllegalReason)  -- 合法でない Action
  | fuelExhausted                     -- 自動処理が上限内に終わらない
  | internal (msg : String)           -- 実装の不整合（WF の下では起きないことを証明対象にする）

/-- 現在の決定要求に対する、プレイヤーの合法手をすべて列挙する（偶然の決定は列挙しない）。 -/
def legalActions (db : CardDB) (s : GameState) : List Action
/-- 決定を 1 つ受け取り、次の決定点まで自動処理を進める。 -/
def step (cfg : EngineConfig) (db : CardDB) (s : GameState) (a : Action) :
    Except RuleError (GameState × List Event)
/-- プレイヤー p から見える情報への射影（128）。 -/
def view (p : PlayerId) (s : GameState) : PlayerView
```

- **カードの集合 `CardDB` は引数で受け取る。**
  - `Riftbound` は具体的なカードを import しない。
  - 定理は「`CardDB.WF db` を満たす任意の `db`」について述べる。
  - 具体的なカード集合が `CardDB.WF` を満たすことは、セットごとに検査する（[roadmap.md](roadmap.md) M7）。
- 自動処理は、`cfg.fuel` を持つ構造再帰の `advance` で回す。
  - 対象: Cleanup の反復（322）、HOT FEPR、Start of Turn、戦闘の各 Step、Expiration Step のループ（317.2.f）、Burn Out の繰り返し（432.3）、Layers の反復（478.3）。
  - fuel が尽きたら `fuelExhausted` を返す。CR には無限ループを処理する規定が見当たらないため、強制ループの検出も兼ねる。
  - 「到達可能な状態では、ある fuel で足りる」という補題は、測度が見つかった部分から積む。
- プレイヤーが自分の意思で続けるループ（同じ起動能力を繰り返すなど）は、決定の列が続くだけなので問題にならない。

### 6.2 決定要求と継続

状態に **継続のスタック** `pending : List Frame` を持つ。先頭のフレームが、いま求めている決定を表す。スタックにするのは、処理が入れ子になるからである。

- コストの支払い中に Add 能力を起動する。Add 能力は Chain に載って即座に finalize・解決し、進行中の処理を一時停止して割り込む（430.2）。
- 解決中の Reflexive Trigger（387）。
- Cleanup や戦闘の途中での選択。

フレームの種類（初期案）:

| フレーム | 内容 |
|---|---|
| `priority p` | Discretionary Action（411.1）を選ぶ: カードのプレイ、能力の起動、Standard Move（144）、Hide（422）、Pass、ターン終了 |
| `playProc` | プレイ手順（354-359）の途中。どの段にいるか、それまでの選択、**巻き戻し用の盤面のスナップショット** |
| `effectResume` | 効果の解決途中。残りの効果と、変数の束縛環境 |
| `cleanupResume` / `combatResume` | Cleanup や戦闘の途中での選択（Showdown / Combat を開く Battlefield: 323.11-12、戦闘ダメージの割り当て: 467.2.c） |
| `choose` | 対象・モード・移動先・プレイ先（355）、任意の追加コストを払うか（355.1.a）、"may" に従うか、誘発能力を Chain に積む順序（383.3.d。戦闘開始時は 466.2.d.1 の例外順）、置換効果の適用順（372）、マリガン（117）、Burn Out で点を与える相手（432.2.c）、Secret / Private なカードへの指示を拒否するか（128.6） |
| `chance` | シャッフル（114）、Main Deck の下へ同時に Recycle するときの順序（417.5）、Burn Out での Trash のランダム化（432.2.b）、手番順（115）、Battlefield のランダムな選択（487.5, 489.5, 490.5, 491.5.a） |

- **`Action` は「行為者 + 内容」とする。** 行為者はプレイヤーか、偶然（chance）。
  - **投了（649-650）は、決定要求と無関係に、残っているどのプレイヤーにも常に合法**とする。
  - 2v2 で味方が行動に招かれる規則（491.8.a）も、行為者として表す。
- **巻き戻し**（358.5）:
  - プレイ手順の開始時に、盤面の部分（決定スタックを含まない）をフレームに保存する。
  - 合法性の確認に失敗したら、それに戻す。
  - 支払い中に起動した Add 能力の効果（Rune の Exhaust、Rune Pool）も戻す。CR は「undone」と書くだけなので、これはモデル上の決定である（[rules-model.md §21](rules-model.md#21-曖昧な点と要確認事項)）。
- 効果を深い埋め込み（§7）で持つので、継続は「残りの効果 + 環境」というデータで表せる。free monad やコルーチンは要らない。

### 6.3 「できること全て」の担保

- **コアは、ルール上の選択をプレイヤーの代わりに決めない。** 選択肢が 1 つしかなくても、決定要求を出す。自動で選ぶ糖衣は Driver が持つ。
- 支払いも、プレイヤーが Rune の Add 能力（164.2: Exhaust で Energy、Recycle で Power）を起動して Rune Pool に資源を出し、そこから払う形で忠実に表す（357, 430, 445）。どの Rune を Exhaust / Recycle するかは戦略上の選択だからである。
- **合法性の仕様 `Legal`**:

  ```lean
  def Legal (db : CardDB) (s : GameState) (a : Action) : Prop
  ```

  - フレームの種類ごとに、CR から直接書く。
  - `step` の実装は参照しない。共有してよいのは、状態の読み出しと特性の導出（`characteristics`）だけ。
  - 人が CR と並べて読める大きさに保つ。これが R2 の主な根拠になる。
  - 偶然の決定の `Legal` は「妥当な順列であること」（`List.Perm`）とし、列挙はしない（40 枚のデッキの順列は列挙できない）。
- **定理の目標**（[roadmap.md](roadmap.md) の I6）:

  | 名前 | 主張 |
  |---|---|
  | `step` の健全性 | `Legal db s a → WF s → ∀ e, step cfg db s a = .error e → e = .fuelExhausted`（合法手は、fuel 切れ以外の理由で拒否されない） |
  | `step` の完全性 | `(∃ r, step cfg db s a = .ok r) → Legal db s a`（合法でない手は受理されない） |
  | 列挙の一致 | `a ∈ legalActions db s ↔ Legal db s a ∧ a.actor ≠ .chance` |

- **`legalActions` を「候補を作って `step` で試し、通ったものを残す」形で定義してはならない。** そうすると列挙の一致の定理が無意味になる。`legalActions` は、フレームの種類ごとに候補を構成的に列挙する。
- `Legal` が未整備のフレームの種類については、その間はテストだけで担保する。どの種類まで整備済みかを、カバレッジ表に出す。

### 6.4 乱数

- コアは決定的に保つ。偶然の決定に対する答え（順列など）を `Action` で受け取り、`Legal`（`List.Perm`）で妥当性を検査する。
- 実行時は、Driver が seed つき乱数で答えを供給する。seed と Action 列があれば対戦を再生できる。
- 定理は「任意の偶然の結果について」を全称量化で述べる。
- 調査した範囲（約 1,100 種のカードテキスト）では、効果に random や shuffle を含むカードは無かった。乱数はルール側にだけ現れる。

### 6.5 隠れ情報

- 状態は全情報で持ち、`view p s` でプレイヤーごとに射影する（128: Secret / Private / Public）。
- 後期の定理目標: プレイヤー p の合法手は `view p s` だけに依存する（隠れ情報が合法手に漏れない）。注意点が 2 つある。
  - 偶然の決定は除外して述べる。
  - ObjId の連番は情報を漏らしうる（例: 山札の中のカードの ObjId から順序が推測できる）。`view` は、見えないオブジェクトの ObjId を隠し、ObjId の付け替えに対して不変な形で定義する。

## 7. 効果 IR（深い埋め込み）

### 7.1 方針

- カード効果は、閉じた帰納型の IR で書く。カードはその値であり、1 つの解釈器が全カードを実行する。
- IR は次の 3 層で構成する。
  1. **プリミティブ**: CR のゲームアクション（408-446）に対応する操作
  2. **結合子**: 列・選択・条件・繰り返し
  3. **キーワード**: 能力へ展開されるマクロ
- **カード固有のコンストラクタ（例: `drawToFull`）は足さない。** IR に足すのはルール上の語彙だけにする。
- カードテキストは長い裾野をもつ。1,779 行の能力文が 1,171 種類のテンプレートに分かれ、そのうち 1,086 種類は 1 回しか現れない。したがって「カードごとのスクリプト」ではなく、合成可能な IR が必須である。
- **`custom` の扱い**:
  - `Effect.custom (id : CustomId) (args : List Arg)` は、ハンドラ表への参照だけを持つ。`Effect` 自体は関数を含まないので、`Repr` やカバレッジ集計が効く。
  - ハンドラは `CardDB` の中の表に置く。中身は「状態と環境を見て、実行すべき IR を返す関数」である。

    ```lean
    structure CustomHandler where
      expand : GameState → Env → Effect
    ```

  - ハンドラの結果は通常の解釈器が実行する。そのため、決定要求は通常どおり外に出る（P4）。`WF` の保存も、IR の補題から自動的に従う。
  - 意味の正しさ（CR とカード文面どおりか）は、`Legal` と、そのカードのシナリオテストで担保する。
  - IR で表せない新しい仕組みが必要なら、`custom` ではなく IR にプリミティブを足す（証明を伴う）。
  - 同じ形のハンドラ（定数だけが違うもの）が 3 つを超えたら、IR の結合子かプリミティブに昇格させる。

### 7.2 構成要素（初期案）

| 要素 | 内容（例） |
|---|---|
| `Effect` | `seq`、`chooseOne`（モード）、`ifThen`、`forEach`、`may`、`doThis`（Reflexive Trigger 387）、`repeat`（820）、プリミティブ、`grant`（継続効果の付与）、`delayed`（遅延能力の生成 390-393）、`custom` |
| プリミティブ | draw、discard、deal、heal、kill、banish、recall、move、ready、exhaust、stun、buff、recycle、channel、add、counter、play、hide、reveal、create、attach / detach、gainXP、score、burn、predict、prevent、replace、copy、double、swap、empower / disempower、takeControl、extraTurn、win |
| `Selector` | 種別、friendly / enemy（740.1）、場所（here、at a battlefield、in bases）、タグ、キーワード、Might の比較、数量（a / up to N / each / all）、Choose（対象を取る）と Pick（取らない）の区別（355） |
| `Amount` | 定数、for each、equal to（Might、コスト）、X |
| `Condition` | 「〜を Control しているなら」、Victory Score までの残り点、Level N、Empowered、Legion、Mighty など |
| `Trigger` | play、attack / defend、conquer / hold、move、die（Deathknell）、フェイズの開始・終了、become Mighty / Empowered、the Nth time |
| `Cost` | Energy、Power（ドメイン指定 / 任意）、exhaust、recycle、discard、味方 Unit の kill、spend XP、spend buff、disempower。追加コスト（必須 / 任意）、割引、増加（356） |
| `Duration` | this turn、this combat、while ...、until ... |
| `Ability` | passive / replacement / activated / triggered（361）と回数制限（once each turn: 371, 386） |
| `StaticMod` | Might 修正、キーワード付与、コスト修正、制限（can't ...）、許可（may play from ...）、Victory Score の修正、得点規則の修正 |

- 変数の束縛は、HOAS（Lean の関数）ではなく名前つき変数（`VarId`）と環境で表す。関数を含む帰納型では `DecidableEq` / `Repr` を導出できず、カードデータの解析もできないためである。
- `Effect` は `List Effect` を含む入れ子の帰納型になる。v4.36.0 では、この形に対して次の 2 点がある（[lean-guidelines.md §5.4](lean-guidelines.md#54-deriving-と等値性)）。
  - `deriving DecidableEq` と `induction` タクティクが使えない。
  - 解釈器と同じ形の相互再帰で書いた定理は通る。

### 7.3 ルールの差し込み口（hook）

「Can't beats Can」（054）を実装する場所を、最初にまとめて決めておく。

- エンジンは導出関数（例: `restrictions db s`、`permissions db s`、`costMods db s`）を通して判定し、カード側は `StaticMod` のデータを持つだけにする。
- 最小版（常に空リストを返すもの）を、最初にプレイを実装するマイルストーン（[roadmap.md](roadmap.md) M4）で作る。

| hook | 例 |
|---|---|
| タイミングの許可 | Action / Reaction、Ambush、Hidden |
| プレイ元ゾーンの許可 | Flow（Trash から）、Champion Zone、Facedown |
| プレイ先・移動先の許可 / 禁止 | Ganking、Deploy、"Units can't be played here"、"Units can't move from here to base" |
| コスト計算 | 356 の各段（置換・追加・増加・割引・総額修正） |
| 対象にできるか | Deflect の追加コスト、Untargetability（756） |
| ダメージ割り当ての制約 | Tank、Backline、"You ignore Tank ..." |
| 得点・勝利 | Victory Score の修正（Aspirant's Climb）、"Players can't score here until their third turn"、Score の置換（Otterpus） |
| 誘発回数 | "Your Deathknell effects trigger an additional time"（Karthus） |

### 7.4 キーワード

- CR は 28 個のキーワードを定める（805-832）。
- `CardDef` は印刷されたキーワードを `List KeywordInst`（キーワードとパラメータの組）として持つ。
  - キーワードは効果で付与・除去されるので（Ability-Altering 層: 479.3）、実効のキーワードは `characteristics` で導出する。
- 意味の与え方は 2 通り。
  - 誘発型・起動型のキーワード（Deathknell、Vision、Equip など）は、能力の列に展開する（`KeywordInst.abilities`）。
  - Passive 型のキーワード（Tank、Assault、Ganking など）は、エンジンの hook が実効のキーワードを参照して扱う。
- パラメータを取るものがある: Assault X、Shield X、Deflect X、Hunt X、Level N、Disarm X、Equip / Repeat / Empower / Flow [Cost]、Show Off [Object]。
- 新しいセットごとに 3〜4 個ずつ増えてきた。追加手順は [card-data.md](card-data.md) に置く。

## 8. 証明を積み上げる方針

段階の詳細は [roadmap.md](roadmap.md) に置く。ここでは層だけを示す。

| 層 | 内容 | 例 |
|---|---|---|
| L0 データ | 判定可能性、コストの算術、デッキ構築の合法性 | 割引の後も Energy と Power が 0 未満にならない（356.6）、デッキ判定の Bool 版と Prop 版の一致 |
| L1 プリミティブ | `moveObj`、draw、recycle、channel、exhaust / ready | WF の保存、物理カードの保存（`List.Perm`）、exhaust の冪等性（415.1.b） |
| L2 手続き | Cleanup、Chain、Priority / Focus、得点 | Chain は後入れ先出し（340.1）、1 人のプレイヤーは 1 つの Battlefield を 1 ターンに高々 1 回 Score する（472）、勝者の一意性 |
| L3 大域 | `Reachable` な状態の `WF`、`Legal` との一致 | §6.3 |
| L4 効果 IR | 解釈器が `WF` を保存する（したがって IR で書いた全カードが `WF` を保存する） | プリミティブの補題からの帰結。`custom` も結果が IR なので同じ |
| L5 関係仕様 | 実装と独立に書いた遷移の仕様との一致 | 戦闘ダメージの割り当て（467）、コスト計算（356）、Layers（478-482） |
| L6 情報 | 隠れ情報の非干渉 | §6.5 |

- **`Reachable`** は帰納的に定義する: 初期状態は到達可能、到達可能な状態から `step` が `.ok` を返した先も到達可能。大域の不変条件は、すべて「初期状態で成り立ち、`step` で保存される」の形で示す。
- **得点の単調性は仮定しない。** CR は得点を失う場合を規定している（194.4.a）。

## 9. ルールとカードの版管理

- **ルール**:
  - コードに `RulesVersion` 定数（`"2026-10-09"`）を置く。
  - 規則番号の引用は常に `(CR 323.4)` の形式で書く。引用はすべてその版を指す。
- **パッチノートが出たとき**:
  1. 公式パッチノートとルール PDF の差分を確認し、影響する規則を Issue にする
  2. 該当モジュールと `Legal` を直し、引用を更新する
  3. 回帰テストを足す
- **Legacy（2027-01）の全面改番**: 引用形式を統一しておけば、スクリプトで抽出・置換できる。旧番号と新番号の対応表を `docs/` に残す。
- **カード**:
  - 印刷テキストと現行テキスト（エラッタ後）を区別する。
  - CardDef には現行テキストに基づく効果を書き、エラッタの出典を記録する。

## 10. カードデータと権利

取り込み手順の詳細は [card-data.md](card-data.md) に置く。権利面の注意点は次のとおり（法的助言ではない）。

- このリポジトリは GitHub 上で **公開（PUBLIC）** されており、ライセンスは Apache-2.0 である。
- Riot の Riftbound 開発者ポリシーは、承認しない用途として「自動ルール適用によるデジタルゲームプレイ」を挙げている。これは API キーを使うプロダクト向けの規定で、研究目的の形式化リポジトリに当てはまるかは不明。
- カード名・カードテキスト・画像は Riot の IP である。Apache-2.0 はコードにだけ適用し、カード由来のデータは対象外と明記する必要がある。
- 推奨:
  - 非商用にする。
  - **リポジトリ直下の `README.md`** に、Riot のファンコンテンツ方針に沿った免責文を置く。
  - カード画像とフレーバーテキストは扱わない。
  - カード全文をリポジトリに入れるかどうかは、§12 の Q1 としてユーザーが判断する。カードの効果を IR で書く作業は、実質的に文面の構造化なので、**Q1 の決着はカードを本格的に入れる M7 の着手条件**とする。

## 11. テストと CI

- 定義と同じ PR で、`#guard` や `example : ... := by decide` による小さな検査を書く。
- **シナリオテスト**: 状態を組み立て、Action 列を流し、結果を検査する。公式 FAQ・裁定を回帰テストにする（例: Radiance Rules FAQ の、置換効果の適用順やコスト支払いの順序）。
- **性質ベーステスト**: Plausible で「ランダムな合法手の列の後でも `WF` が成り立つ」を検査する。証明に先立って誤りを早く見つけるためである。
- **CI**: `leanprover/lean-action` で build・test・axiom 監査を行う。加えて、`sorry` の検出、カードデータの陳腐化検査、実装カバレッジ表（カードと `Legal` の整備状況）の生成を行う。

詳細は [lean-guidelines.md](lean-guidelines.md) に置く。

## 12. 未決事項（ユーザーの判断が要るもの）

| # | 論点 | 推奨 |
|---|---|---|
| Q1 | カード名・カードテキストを公開リポジトリにコミットするか | M6 まではルールの中核とテスト用の少数カードだけで進める。M7 に入る前に方針を決める（§10） |
| Q2 | 初期スコープを 1v1（Duel）に絞ってよいか | 型と手番の走査は最初から N 人対応で作り、実装と定理は 1v1 から始める。多人数固有の規則は M9 |
| Q3 | Mathlib を依存に入れるか | 入れない（core + Std + Plausible）。`Finset` などが本当に必要になったら再判断する |
| Q4 | Core Rules の Legacy 改訂を待つか | 待たない。2026-10-09 版で始め、改訂時に追従する |
| Q5 | Tournament Rules（Main Deck ちょうど 40 枚、Battlefield 3 枚など）をどこまで扱うか | Core Rules（40 枚以上）を正とし、大会規定は別の述語として後から足す |

## 13. リスクと対策

| リスク | 対策 |
|---|---|
| セットごとのルール改訂 | §9 の版管理。規則番号の引用を機械的に追えるようにする |
| `Legal` の記述量が大きくなる | フレームの種類ごとに少しずつ整備し、整備状況をカバレッジ表で見えるようにする。未整備の間はテストで担保する |
| Layers の依存関係（480-481）の実装が難しい | timestamp 順で始め、依存が必要なカードが出た時点で実装する。関係仕様（L5）で検証する |
| 効果 IR の表現力不足 | 動的な組み立ては `custom` で逃がし、頻出したら IR に昇格させる。新しい仕組みは IR のプリミティブとして足す |
| 証明コストの膨張（Cedar の例では証明がモデルの約 3.4 倍） | 証明はプリミティブと手続きに集中させ、カード単位の証明義務をほぼゼロにする |
| 巨大な列挙型での `deriving` の性能（`LawfulBEq` の証明は構築子数の二乗で重くなり、`DecidableEq` の導出が遅いという報告もある） | カードを構築子にしない。カードはデータとして持つ |
| 入れ子の帰納型（`List Effect` を持つ `Effect`）では、v4.36.0 の `deriving DecidableEq` と `induction` タクティクが使えない（ローカルで確認） | 等値性は手書きするか、専用のリスト型を `mutual` で定義する。帰納法の代わりに、相互再帰の定理で書く（[lean-guidelines.md §5.4](lean-guidelines.md#54-deriving-と等値性)） |
| 権利 | §10。公開範囲をユーザーが決める |
