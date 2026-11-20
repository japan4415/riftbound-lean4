# Riftbound Lean4 実装方針

本書は、要求の正本である [`docs/original.md`](original.md) を前提にした実装方針である。`original.md` は人間だけが編集する。本書と食い違う場合は `original.md` を優先する。

関連文書:

- [rules-model.md](rules-model.md) — Riftbound Core Rules を形式化の観点で整理したもの（規則番号つき）
  - 本書で定義なしに使うルール用語（Chain、Pending / Finalize、HOT FEPR、Cleanup、Contested、Staged、Showdown、Mighty など）は、こちらを参照。
- [tournament-model.md](tournament-model.md) — Riftbound Tournament Rules のうち形式化の対象にする部分（フォーマット、マッチ、時間切れ、ループ）
- [lean-guidelines.md](lean-guidelines.md) — このリポジトリの Lean 4 コーディング規約
- [card-data.md](card-data.md) — カードデータの取り込みと、効果 IR への落とし込み
- [roadmap.md](roadmap.md) — マイルストーンと、証明を積み上げる順序

---

## 1. 要求の整理

`original.md` の要求を次の 5 つに分ける。

| ID | 要求（original.md） | 設計上の解釈 |
|---|---|---|
| R1 | Lean4 で実装する | 実行できるルールエンジンと、その性質の証明を、同じ Lean コードベースに置く |
| R2 | ルールは公式のルールに則る | 公式ルールは Core Rules と Tournament Rules の両方とする。各定義から規則番号を辿れるようにする。合法性は、ルールから直接書いた仕様 `Legal` として独立に持つ。ルール改訂に追従する手順を持つ |
| R3 | 新カードの追加時にその効果を反映できる | カードは「データ + 効果 IR（中間表現）」で表す。エンジンはカードの集合（`CardDB`）を引数に取り、定理はすべての `CardDB` について述べる。新カードの追加は、原則としてデータの追加で済ませる |
| R4 | 小さいところから証明を積み上げる | ゾーン移動などのプリミティブで一度だけ証明し、手続き・大域不変条件・カードへと積み上げる |
| R5 | 全カードをコード化し、カードでできること全てができる | エンジンはプレイヤーの選択肢を勝手に狭めない。すべての選択を決定要求として外に出し、合法手を漏れなく列挙する |

R5 の「できること全て」は、本書では次の 2 点の両立と定義する。

1. **表現の完全性**: 全カードの効果がモデル上に存在する（[roadmap.md](roadmap.md) の最終マイルストーンで判定する）。
2. **選択の完全性**: CR 上プレイヤーに許される選択は、すべて合法手として現れる。次の 2 つに分けて担保する（§6.3）。
   - **答えの合法性**: エンジンが出した問い（決定要求）に対して、どの答えが合法かを、仕様 `Legal` として CR から直接書く。構成的な列挙 `legalActions` と `Legal` の一致を定理で示す。
     - `step` と `legalActions` の間の整合だけでは、両方が同じ手を落としていても成り立ってしまう。だから独立した仕様が要る。
   - **問いの正しさ**: 正しい相手に、正しい時点で問いが出ること。`Legal` は問い（フレーム）ごとに書くので、これは `Legal` との一致からは出てこない。決定点についての定理（[roadmap.md](roadmap.md) の I16〜I18）とシナリオテストで担保する。

## 2. 前提とするバージョン

| 対象 | 版 | 備考 |
|---|---|---|
| ルール | **Riftbound Core Rules, Last Updated 2026-10-09**（Radiance 版、2026-10-16 発効） | 以下「CR」と略す。規則番号はすべてこの版のもの |
| 大会のルール | **Riftbound Tournament Rules, Last Updated October 9, 2026** | 以下「TR」と略す。大会では CR に優先する（TR 104.1）。[tournament-model.md](tournament-model.md) |
| カードプール | Origins, Proving Grounds, Spiritforged, Unleashed, Vendetta, Radiance | 2026-11-20 時点。公式ギャラリー上で 1,416 件の印刷、論理カードは約 1,100 種 |
| Lean | `leanprover/lean4:v4.36.0` | 2026-11-16 公開の最新 stable。ローカルの elan 既定と一致 |

近い将来の変化:

- **2027-01-29 発売の Legacy で、Core Rules の書式が全面的に刷新されると予告されている。** メカニクスは変えないとされるが、規則番号は大きく変わる見込み。
- 同時にカード文面のテンプレートも変わる。例: "When you play me" は "When I enter" に、トークンの生成は "Play" から "Create" に変わる。
- どちらも §9 の版管理で吸収する。改訂を待たずに着手してよい。

## 3. 設計原則

| # | 原則 | 理由 |
|---|---|---|
| P1 | **状態遷移は実行できる関数 `step` で定義し、合法性は公式ルール（CR / TR）から直接書く仕様 `Legal`（`Prop`）として独立に持つ。** `step` は答えを受理するかどうかを `Legal` の決定手続きで決める。構成的な列挙 `legalActions` と `Legal` の一致を定理として積む（§6.3）。遷移そのものを関係で書く仕様は、検証したい一部（戦闘ダメージなど）にだけ足す | `#eval` で対戦を進められ、`simp` で展開できる。合法性の仕様が実装と独立していれば、R2 と R5 の根拠になる。受理の判定に仕様を使えば、合法性を書く場所が 2 つで済む |
| P2 | **状態は素直なデータにし、不変条件は別の述語で持つ。** どの中間状態でも成り立つ構造の条件 `WF` と、Cleanup の不動点で成り立つ条件 `Settled` を分ける（§5.2）。依存型で縛るのは `Fin` などの葉に限る | 失敗しうる遷移（`Except`）と相性がよい。カード追加のたびに証明を求められない。規則上は一時的に破れる条件を `WF` に入れると、`step` が `WF` を保存しなくなる |
| P3 | **エンジンはカードを知らない。** カード名で分岐せず、カードの集合 `CardDB` を引数で受け取る。ルールを曲げるカードのための差し込み口（hook）を最初から用意する | 成熟した TCG エンジン（MTG Arena の GRE、Argentum Engine）がこの形で拡張性を得ている。定理を特定のカード集合に固定しないためでもある |
| P4 | **プレイヤーの選択はすべて明示的な決定要求にする。** 状態の中に「誰が何を決める番か」を継続のスタックとして持ち、`Action` で答えを受け取る。**コアは選択を自動で決めない**（自動化は Driver の機能） | R5（選択の完全性）。直列化・再生・合法手の列挙が容易になる |
| P5 | **乱数をコアに持たない。** シャッフルなどは「偶然の決定」として外から結果を受け取り、エンジンは妥当性（置換であること）だけを検査する | `step` が決定的な全域関数のままになり、「どのシャッフル結果でも成り立つ」を量化で述べられる |
| P6 | **ゾーン移動は 1 つのプリミティブ `moveObj` に集約する。** `moveObj` は移動後の ObjId を返す | 保存則・一意性を一度だけ証明すれば、それを使う全効果・全カードに効く |
| P7 | **規則番号を辿れるようにする。** 各定義の docstring に `(CR 323.4)` や `(TR 402.1)` の形で根拠を書く | 公式ルールへの準拠（R2）を確認でき、改訂時の影響範囲を機械的に洗い出せる |
| P8 | **検証コアに `partial` / `unsafe` / `native_decide` / `sorry` を入れない。** axiom は、ローカルの検証で監査する（§11） | `partial` な定義は kernel から不透明で証明できない。`native_decide` はコンパイラを信頼対象に加えてしまう |
| P9 | **盤面の変更は、すべてイベントの経路 `perform` を通す**（提案 → 置換・防止 → 適用 → 発行。§6.6）。置換の段は、最初から空の実装で用意する | 置換効果（367-375）と Prevent（438）は、起きる前のイベントを書き換える。経路を後から足すと、全プリミティブの補題を書き直すことになる |

## 4. 全体構成

```text
 カードデータ（公式ギャラリー等）
        │  scripts/（uv + Python）: 取得・正規化・Lean 生成
        ▼
 RiftboundCards（ライブラリ）: 1 弾 1 ファイルの CardDef と、具体的な CardDB
        │ CardDB を引数として渡す（Riftbound 側は RiftboundCards を import しない）
        ▼
 Riftbound（検証コア）
   Core ─→ Card ─→ State ─→ Rules ─→ Spec ─→ Engine ─→ Invariant
   基本型   効果IR   状態・    手続き・  Legal     step /        WF の保存・
            CardDef  フレーム・ 1 歩の   （CR から  legalActions  一致の定理・
            CardDB   Action    解釈器    直接書く） / view        Reachable
 RiftboundDriver（ライブラリ）: 乱数の供給、自動対戦、ログ再生（IO を使う。検証の対象外）
 RiftboundTest: シナリオ・公式 FAQ の回帰・性質ベーステスト
```

矢印は import の向き（左が右に import される）。循環を避けるため、層を次の順に固定する。

1. `Core`: ID、Domain、CardType、Keyword、Cost、Mode などの基本型
2. `Card`: 効果 IR、値と環境（`Value`、`Env`）、`CardDef`、`CardDB`。**この層は `GameState` を参照しない**（§7.1）
3. `State`: オブジェクト、ゾーン、イベント、決定要求と継続（フレーム）、`Action`、`GameConfig`、`GameState`、`WF` と `Settled`
4. `Rules`: 手続きと、効果の 1 歩の解釈器（`microStep`）
5. `Spec`: 合法性の仕様 `Legal`。下の層から使うのは、状態の読み出し、特性の導出（`characteristics`）、hook の導出関数だけ
6. `Engine`: `step`、`legalActions`、`view`
7. `Invariant`: 不変条件の保存と、一致の定理

`Action` を State 層に置くのは、Rules 層（プレイ手順の再開、時間切れ）と Spec 層がこの型を使うからである。

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
    Mode.lean                  -- Mode のデータ部分（人数、Victory Score、Battlefield の枚数: 483-491）
  Card/
    Syntax.lean                -- Effect / Selector / Amount / Condition / Trigger / Duration / Cost式 / 選択の宣言
    Value.lean                 -- Value と Env（変数の束縛環境）
    Ability.lean               -- Ability
    CardDef.lean               -- CardDef
    CardDB.lean                -- CardDB（カード定義と custom ハンドラの表）と、その整形性 CardDB.WF。GameState を参照しない
  State/
    Object.lean                -- ゲームオブジェクト（種別: カード / トークン / Chain 上の能力）、ステータス
    Zone.lean                  -- ゾーン（105-109）と Location（197-200）
    Event.lean                 -- イベント（提案と発行の両方に使う。§6.6）
    Decision.lean              -- 決定要求と継続のフレーム
    Action.lean                -- Action（行為者 + 内容）
    GameConfig.lean            -- RuleSet / GameConfig と、設定の妥当性
    GameState.lean
    WF.lean                    -- 構造の不変条件 WF と、Cleanup の不動点の条件 Settled
  Rules/
    Move.lean                  -- 唯一のゾーン移動プリミティブ moveObj
    Perform.lean               -- イベントの経路 perform（提案 → 置換・防止 → 適用 → 発行）
    Actions/*.lean             -- ゲームアクション（408-446）: Draw, Recycle, Channel, Burn Out ...
    Characteristics.lean       -- Layers による実効特性の導出（475-482）
    Interp.lean                -- 効果の 1 歩の解釈器 microStep（再帰しない。§6.1）
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
    Modes.lean                 -- ゲームモードごとの手続き（483-491）
  Spec/
    Legal.lean                 -- 合法性の仕様（決定の種類ごとに CR から直接書く）
    Combat.lean ...            -- 遷移の関係仕様（必要な部分だけ）
  Engine/
    Step.lean  LegalActions.lean  View.lean
  Invariant/                   -- WF の保存、一致の定理、Reachable
  Match/
    Basic.lean                 -- マッチの骨格: ゲームの結果の列から、マッチの結果と次のゲームの準備を決める（CR 488, TR 404）。Engine 層の後
  Tournament/                  -- Tournament Rules（tournament-model.md）。import 上の位置はファイルごとに違う
    Format.lean                -- フォーマット（Constructed / Sealed / Draft）と、フォーマットによるゲーム中の変更。Card 層の直後（GameConfig が参照する）
    DeckLegality.lean          -- フォーマットごとのデッキの合法性、カードの合法性、禁止カード（TR 402, 403, 601, 602）。Card 層の直後
    TimeLimit.lean             -- 時間切れの手順（TR 408）。Rules 層（ターンの進行の中で数える）
    Loop.lean                  -- ジャッジによるループの引き分け（TR 505.6）。Rules 層
    LoopDetect.lean            -- 決定点をまたぐ、強制的なループの検出器（tournament-model.md §5）。Engine 層の後。Driver が使う
    Match.lean                 -- 大会のマッチの手続き: サイドボード、先手の決め方、時間切れ時の判定（TR 403, 406, 407, 408.3, 410.2）。Match/Basic の後
RiftboundCards/
  Origins.lean ProvingGrounds.lean Spiritforged.lean Unleashed.lean Vendetta.lean Radiance.lean
                               -- 1 弾 1 ファイル。カードごとに公式文面（docstring）と効果を並べる（card-data.md §4）
  Tokens.lean                  -- トークンの定義（CR 187）
  Registry.lean                -- 具体的な CardDB
RiftboundDriver/               -- 乱数の供給、自動対戦、ログ再生（`Trace.lean` が 1 ゲームを JSON に書き出す。`viewer/` が再生する: viewer.md）
RiftboundTest/
  Scenario/  Faq/  Property/
Main.lean                      -- CLI（後期）
scripts/                       -- カードデータの取得・Lean 生成・カバレッジ集計（uv 管理）と、全体の検証（verify.sh）
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
| `CardId` | 論理カード（カード定義）。トークンの定義にも CardId を振る | 印刷違い（showcase、alt-art、signature など）は同じ CardId にまとめる。値の決め方は [card-data.md §3](card-data.md#3-取り込みのパイプライン) |
| `Timestamp` | 効果が適用され始めた時点（482） | 状態の中のカウンタ `nextTimestamp` から払い出す |

ObjId の払い出しで、次の 2 つの性質がデータ構造から直接出てくる。

- 「Non-Board ゾーンを経由して戻ったものは別オブジェクトで、対象として不正」（359.3.e）
- 一時的な修正がすべて失われること（124.1）

古い ObjId の行は表から消える。後から参照する情報は、次のように値として受け渡す。

- `moveObj` は、移動後の新しい ObjId を返す。移動したカードを後続の指示が参照するときは、解釈器がそれを変数に束縛する。
- 誘発した時点の情報（359.3.f）は、誘発能力を Chain に載せるときに、値として `Env` に写す（例: 死んだ Unit の Might）。

### 5.2 ゾーンとオブジェクト

- **ゾーンの中身は `List ObjId` で持ち、これを真実の源にする。** Main Deck・Rune Deck・Chain のように順序があるゾーンも同じ表現にする。
- CR のゾーンに加えて、エンジン内部用のゾーンを 2 つ持つ（どちらもプレイヤーごと）。
  - **`setAside`**: マリガンで脇に置いたカード（117.1）などを入れる。
  - **`outOfGame`**: ゲームの外にある物理カードを入れる。構築時に追加で選んだ Legend（103.1）や、除去の手順で置き換えられた Battlefield（652）など。物理カードの保存（[roadmap.md](roadmap.md) の I1）は、このゾーンを含めて述べる。
- **オブジェクトの表**: 属性は ObjId をキーとする表に置く。型は `Std.ExtTreeMap ObjId Object` とする（[lean-guidelines.md §5.3](lean-guidelines.md#53-データ構造)）。
  - 種別: カード（PhysId と CardId を持つ）、トークン（CardId を持つ）、Chain 上の能力（発生源と能力への参照を持つ）。
  - 属性: Owner、Controller（基底の値）、ステータス、ダメージ、カウンター、Attach 先、timestamp など。
- **Controller は、表には基底の値を保存する。**
  - Control を変える継続効果は、Trait-Altering 層で適用する（479.2）。
  - 規則の判定（friendly / enemy、Priority、Contested、Recall 先など）は、`characteristics` で導出した実効の Controller を使う。表の値を直接読まない。
  - friendly / enemy を参照する効果は Ability-Altering 層以降にあり、Trait-Altering 層で Controller が決まった後に評価される。だから循環しない。Trait-Altering 層の中で Controller を参照する効果が現れたら、依存関係（480-481）として扱う。
- **不変条件は 2 つの述語に分ける。**
  - **`WF`（構造の条件）**: どの中間状態でも成り立つ。`step` と、その中の 1 歩（`microStep`）が保存する。
    - 全ゾーンの列を連結したものが `Nodup` である（位置の一意性）
    - 表の定義域が、ゾーン上の ObjId の集合と一致する
    - すべての ObjId が `nextId` 未満で、すべての timestamp が `nextTimestamp` 未満である
  - **`Settled`（Cleanup の不動点の条件）**: `priority` フレームが先頭にある状態で成り立つ（[roadmap.md](roadmap.md) の I17）。効果の解決の途中などでは、破れていてよい。
    - 致死ダメージを負った Unit がいない（323.4）
    - Control を失うべき Battlefield が残っていない（323.5）
    - Recall の対象が残っていない（323.6）
    - 各 Facedown Zone の中身が、その時点の最大容量を超えない（容量は効果で増減する: 107.3.b）
    - Attach 関係が整合している（Attach 先が Board 上にある。Unit は Attach されない: 143.5）
  - 分ける理由: 後者は規則の上で一時的に破れる。たとえば容量を決める Passive の持ち主が盤面を離れると、超過分を Trash に置くまでの間は容量を超えている。`step` は効果の解決の途中の決定点でも戻るので、これを `WF` に入れると `step` が `WF` を保存しなくなる。
  - Attach の後始末がどの時点で起きるか（716-719）は、Attach を実装するとき（[roadmap.md](roadmap.md) M8a）に原文で確かめる。離れるのと同時に外れるなら、Attach 先の存在は `WF` の側へ移す。
  - どちらも `Decidable` にし、テストで実行時の検査に使う。
- **所有者の不変条件 `OwnerOk`**（CR 056）: Non-Board ゾーンにあるカードの Owner は、そのゾーンの持ち主である。`WF` とは別の述語で、`moveObj`（行き先を Owner のゾーンに直す）、並べ替え、`addObject`、`step` が保つ。`step` の健全性（合法な答えは fuel 切れ以外で拒否されない）は、`WF` と `OwnerOk` の下で示す。
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
| 対局の規則 | `config : GameConfig`（ルールとモード）。初期状態で決め、対局中は変えない（§6.1） | 483-491、TR 104.1 |

方針: 導出できるものは保存しない（冗長な状態は不変条件を増やすため）。

### 5.4 特性の導出（Layers）

- 実効特性は `characteristics : CardDB → GameState → ObjId → Characteristics` で毎回導出する。
  - 基底は CardDef の印刷値。
  - その上に 4 層を順に適用する（479）: Copy → Trait-Altering → Ability-Altering → Arithmetic。
  - 他のオブジェクトの情報に依存する効果がある（478.1）。だから定義は全オブジェクトを一度に評価し、`characteristics` はその結果から引く。
  - **1 巡で終わりではない。** 適用によって新たに適用可能になった効果があれば、変化がなくなるまで層の評価を繰り返す。ただし各効果の適用は 1 回だけで、除去も 1 回だけである（478.2-478.4）。
  - **反復の上限は内側で決める。** 適用も除去も 1 回だけなので、反復は「継続効果の数 × 2 + 1」巡で必ず止まる。この上限で回し、外から fuel は受け取らない。`characteristics` は失敗しない全域の関数のままで、これを共有する `Legal`（§6.3）も fuel に依存しない。
- 継続効果の扱い:
  - **Passive** は保存せず、盤面上のオブジェクトから導出する。timestamp は、そのオブジェクトの記録（Board に出た時点や、Inactive から戻った時点: 482.2）を使う。
  - **期間つき効果**（"this turn" など）は、「効果 + timestamp + 期間」のリストとして状態に保存する。失効はリストから取り除くだけで済む。
- 同一層内の依存関係（480-481）は、まず timestamp 順（482）だけで実装する。依存の判定は、それが必要なカードが来た時点で実装する（[roadmap.md](roadmap.md) M6）。
- **導出値への誘発**（「Mighty になったとき」: 709 など）は、1 歩（`microStep`）の前後で `characteristics` を比べて検出する。前の値は保存しない。1 歩の中では、前後の状態が両方手元にあるからである。

## 6. エンジンの形

### 6.1 中核 API

```lean
/-- どのルールで遊ぶか。 -/
inductive RuleSet where
  | coreOnly                       -- Core Rules だけ
  | tournament (format : Format)   -- Tournament Rules を Core Rules に優先して適用する（TR 104.1）

/-- 対局の規則。初期状態（`GameState.config`）に入れ、対局中は変えない。 -/
structure GameConfig where
  ruleSet : RuleSet
  mode    : Mode                   -- Duel などのゲームモード（CR 483-491）

/-- ゲームの終わり方。Core Rules には勝利しかないが、大会のルールでは引き分けがある。 -/
inductive GameResult where
  | won (winners : List PlayerId)  -- 2v2 では勝者はチーム（CR 491.6.a）
  | draw (reason : DrawReason)     -- ループ（TR 505.6）、時間切れ（TR 408.2.b）、合意（TR 410.1）

inductive RuleError where
  | illegal (reason : IllegalReason)  -- 合法でない Action
  | fuelExhausted                     -- 自動処理が上限内に終わらない
  | internal (msg : String)           -- 実装の不整合（WF の下では起きないことを証明対象にする）

/-- 現在の決定要求に対する、プレイヤーの合法手をすべて列挙する（偶然・時計・ジャッジの Action は列挙しない）。
M2b の実装は `CardDB` を取らない（カードの文面を使う決定が入る M4 で足す）。 -/
def legalActions (db : CardDB) (s : GameState) : List Action
/-- 自動処理を 1 歩だけ進める。再帰しない。 -/
def microStep (db : CardDB) (s : GameState) : Except RuleError (GameState × List Event)
/-- 決定を 1 つ受け取り、次の決定点まで自動処理を進める。fuel は、進める歩数の上限。 -/
def step (fuel : Nat) (db : CardDB) (s : GameState) (a : Action) :
    Except RuleError (GameState × List Event)
/-- プレイヤー p から見える情報への射影（128）。 -/
def view (p : PlayerId) (s : GameState) : PlayerView
```

- **対局の規則と fuel を分ける。**
  - 対局の規則（`GameConfig`: ルールとモード）は、初期状態に入れる。`step` はこれを変えない。`Legal`、`legalActions`、手続きは、規則を `s.config` から読む。
  - 規則を `step` の引数にしないのは、対局の途中で規則を変えられる型にしないためである。合法性は規則に依存する（合意の引き分け、時計、2v2 の招待）ので、`Legal` と `legalActions` も同じ規則を見る必要がある。
  - 成り立たない組合せを除くために、設定の妥当性 `GameConfig.Valid` を置く（TR が手続きを定めていない、モードとフォーマットの組など。どの組が有効かは TR 600 番台で確かめる）。
  - fuel は実行時の引数で、状態には入れない。
- **カードの集合 `CardDB` は、対局の規則（`GameConfig`）と同じく、対局の固定の部分として扱う。**
  - **実装（2026-11-21、M4a）**: `CardDB` は引数で渡さず、`GameState.cards` に入れた。`GameState.initial db config decks` が入れ、`step` と `Legal` と `legalActions` の引数は増やさない。対局の途中では変わらない（`SameMeta` が保つ）。理由は、`step`・`advance`・`microStep`・`Legal`・`Reachable` のすべてに `db` を通す書き換えが、不変条件の証明 3,000 行に及ぶためで、得るものは何も無い。定理は「`CardDB.WF` を満たす任意の `s.cards`」について述べることになり、引数で渡す形と同じ強さである。
  - 以下の「引数で受け取る」は、この実装では「状態から読む」と読み替える。
  - `Riftbound` は具体的なカードを import しない。エンジンは、カード名で分岐せず、`GameState.cards` から読んだ定義だけで動く。
  - 定理は「`CardDB.WF db` を満たす任意の `db`」について述べる。`CardDB.WF` は判定可能な静的な条件だけからなる（§7.1）。
  - 具体的なカード集合が `CardDB.WF` を満たすことは、セットごとに検査する（[roadmap.md](roadmap.md) M7）。
- **自動処理は、1 歩の関数 `microStep` を fuel の回数だけ繰り返して進める。**
  - `step` は 3 つの段からなる: 答えを受理するかを判定する（§6.3）→ 答えをスタックの先頭のフレームに適用する → `advance` を呼ぶ。
  - `advance` は、スタックの先頭が決定のフレームになるか、対局が終わるまで、`microStep` を繰り返す。fuel についての構造再帰で書く。
  - `microStep` が進めるもの: 効果の解決（列、繰り返し、`custom` の展開、置換の指示、効果の中でのプレイ）、Cleanup の反復（322）、HOT FEPR、Start of Turn、戦闘の各 Step、Expiration Step のループ（317.2.f）、Burn Out の繰り返し（432.3）。
  - 効果の解決も 1 歩ずつ進める。`custom` の展開や置換の指示は別の `Effect` を実行するので、`Effect` の構造再帰では書けない（[lean-guidelines.md §5.1](lean-guidelines.md#51-再帰と停止性)）。継続は「残りの効果 + 環境」というデータなので（§6.2）、1 歩の関数にできる。
  - Layers の反復（478.3）だけは別で、内側の上限で止まる（§5.4）。
  - fuel が尽きたら `fuelExhausted` を返す。
  - **fuel の単調性**（[roadmap.md](roadmap.md) の I15）: ある fuel で `.ok r` なら、それ以上のどの fuel でも同じ `.ok r` を返す。`Reachable`（§8）と `Legal` との一致（§6.3）が fuel の選び方によらないことは、この補題による。
  - 「到達可能な状態では、ある fuel で足りる」という補題は、測度が見つかった部分から積む。
- **ループ**:
  - CR には無限ループを処理する規定が見当たらない。Core Rules だけの設定では、止まらない自動処理は `fuelExhausted` になる。
  - 大会のルールでは、誰も断たず、誰も維持していないループは引き分けになる（TR 505.6）。これは、**ジャッジを行為者とする `Action`** として外から受け取る（§6.2）。エンジンは自動では検出しない。
  - 検出しない理由は 2 つある。状態は完全には繰り返さない（周回ごとに新しい ObjId と timestamp を払い出す）。また、誘発のループは Priority のパスという決定を毎周はさむので、自動処理の中に収まらない。詳しくは [tournament-model.md §5](tournament-model.md#5-ループtr-505)。
  - 自動対戦のための検出器は、エンジンの外に別の関数として置く（同 §5）。
- プレイヤーが自分の意思で続けるループ（同じ起動能力を繰り返すなど）は、決定の列が続くだけなので問題にならない。

### 6.2 決定要求と継続

状態に **継続のスタック** `pending : List Frame` を持つ。スタックにするのは、処理が入れ子になるからである。

- コストの支払い中に Add 能力を起動する。Add 能力は Chain に載って即座に finalize・解決し、進行中の処理を一時停止して割り込む（430.2）。
- 解決中の Reflexive Trigger（387）。
- Cleanup や戦闘の途中での選択。

フレームには 2 種類ある。先頭が **決定のフレーム** なら、`step` は答えを待つ。先頭が **作業のフレーム** なら、`microStep` が 1 歩進める（§6.1）。

フレームの種類（初期案）:

| フレーム | 種別 | 内容 |
|---|---|---|
| `priority p` | 決定 | Discretionary Action（411.1）を選ぶ: カードのプレイ、能力の起動、Standard Move（144）、Hide（422）、Pass、ターン終了 |
| `choose` | 決定 | 対象・モード・移動先・プレイ先（355）、任意の追加コストを払うか（355.1.a）、"may" に従うか、誘発能力を Chain に積む順序（383.3.d。戦闘開始時は 466.2.d.1 の例外順）、置換効果の適用順（372）、マリガン（117）、Burn Out で点を与える相手（432.2.c）、Showdown / Combat を開く Battlefield（323.11-12）、戦闘ダメージの割り当て（467.2.c）、Secret / Private なカードへの指示を拒否するか（128.6） |
| `chance` | 決定（偶然） | シャッフル（114）、Main Deck の下へ同時に Recycle するときの順序（417.5）、Burn Out での Trash のランダム化（432.2.b）、手番順（115）、Battlefield のランダムな選択（487.5, 489.5, 490.5, 491.5.a） |
| `chooseBurnOut` | 決定 | Burn Out で点を与える相手（432.2.c）。`chanceBurnOut`（Trash を山札に戻す順序: 432.2.b。答えた時点で Recycle する）の次に積まれる |
| `priority p` | 決定 | Main Phase で、手番のプレイヤーが Priority を持つ（311-312, 316）。答えは `pass`（Chain が無いので、Main Phase を終えて Ending に進む: 305）か、Basic Rune の Add 能力（`runeAbility`: Exhaust で Energy、Recycle で Power: 164.2。即座に解決し、`priority` のまま）。Discretionary Action（カードのプレイなど）は M4 で足す |
| `beginTurn` / `phase ph` | 作業 | 次のターンを始める（手番のプレイヤーは手番順を回す: 118, 301）。各フェイズの処理（Awaken: Ready、Channel、Draw、Ending: Heal。314-317） |
| `setupHands` / `draw p n` | 作業 | 開幕の手札とマリガンの並べ方（116-117）、`p` が `n` 枚引く（414）。空の山札に当たると Burn Out のフレームを積む（432） |
| `playProc` | 作業 | プレイ手順（354-359）の途中。どの段にいるか、それまでの選択、**巻き戻し用の盤面のスナップショット** |
| `effectResume` | 作業 | 効果の解決途中。残りの効果と、変数の束縛環境 |
| `cleanupResume` / `combatResume` | 作業 | Cleanup や戦闘の途中。どの手順にいるか。HOT FEPR のタスクも同じ形で持つ |

作業のフレームは、選択が必要になると、その上に決定のフレームを積む。

- **フレームは、盤面のデータを持たない。** `mulligan p n` は選んだ枚数だけを持ち（選んだカードはその場で脇に置く）、並べ替えのフレームはゾーンを指すだけで、並べるカードは答えのときにゾーンから読む。盤面の写しを持つと、フレームが積まれてから答えられるまでの間に盤面が変わったとき、写しが古くなる。写しが無ければ、フレームの正しさを別の不変条件として保つ必要がない（`step` の健全性の証明が、`WF` と `OwnerOk` だけで済む理由）。
- **決定のフレームは「問い」だけを持ち、候補の一覧を持たない。**
  - 対象なら Selector と制約、順序なら並べるもの、という形で持つ。分割した決定（下記）では、それまでの選択も持つ。
  - 候補は、`Legal` と `legalActions` がそれぞれ盤面から計算する。
  - フレームに候補を持たせると、`Legal` が「候補に含まれること」になり、候補の計算の誤りを見逃す（§6.3）。
- **決定の粒度**: 1 つの `Action` は、小さな有限の候補から 1 つを選ぶ形にする。
  - 答えが組合せになる決定は、「次の 1 つを選ぶ」決定の列に分ける。対象は、戦闘ダメージの割り当て（467.2.c）、複数の Unit の同時の Standard Move（144.3）、同時に誘発した能力の順序（383.3.d）、Rune Deck へ戻す順序（417.5.a）、"up to N" や "any number" の対象（355.13）、マリガンで脇に置くカード（117）である。
  - 列の途中では、Cleanup も誘発も走らせず、盤面も変えない。選択はフレームにためておき、列が終わった時点で 1 つのアクションとして実行する。規則上の同時性は変わらない。
  - 分けないと、`legalActions` の列挙が組合せの数だけ膨らむ。偶然の決定を列挙しないのと同じ理由である（§6.3）。
- **`Action` は「行為者 + 内容」とする。** 行為者は、プレイヤー、偶然（chance）、時計（clock）、ジャッジ（judge）のいずれか。
  - **投了（649-650）は、決定要求と無関係に、残っているどのプレイヤーにも常に合法**とする。1v1 では相手が勝ち、スタックが空になる。終わったゲームは、どんな答えも違法（M3 前半で実装。3 人以上は M9）。
  - 大会のルールでは、合意による引き分け（TR 410.1）も、決定要求と無関係に提案できる。全員が同意したらゲームを `draw` で終える。
  - 時計は、時間切れ（TR 408.2）を知らせる行為者である。以後、エンジンが残りターン数を数え、終わったら点差で結果を決める。
  - ジャッジは、ループによる引き分け（TR 505.6）を宣言する行為者である。時計と同じく、判断の根拠（誰もループを断たず、誰も維持しないこと）はエンジンの外にある。大会の設定でだけ合法とする。
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

  - 決定のフレームの種類ごとに、CR（大会の設定では TR も）から直接書く。どのルールで遊んでいるかは `s.config` から読む。
  - `step` の実装は参照しない。共有してよいのは、状態の読み出し、特性の導出（`characteristics`）、hook の導出関数（§7.3）だけ。
  - 候補はフレームから読まず、盤面から計算する（§6.2）。
  - 分割した決定（§6.2）では、「その選択を含む、完全で合法な答えが存在すること」を合法とする。決定的に不正になる選択はできない（355.16）という規則を、列の各段に当てはめたものである。行き止まりの選択を合法にしないので、進行性（I5）も保たれる。
  - 人が CR と並べて読める大きさに保つ。これが R2 の主な根拠になる。
  - `Decidable` のインスタンスを付ける。
  - 偶然の決定の `Legal` は「妥当な順列であること」（`List.Perm`）とし、列挙はしない（40 枚のデッキの順列は列挙できない）。
- **受理の判定には `Legal` を使う。** `step` は、答えを受理するかどうかを `Legal` の決定手続き（`decide (Legal db s a)`）で決める。
  - 合法性を書く場所が 2 つで済む（`Legal` と `legalActions`）。`step` の中に 3 つ目の検査を書かない。
  - 独立に書いた 2 つ（仕様 `Legal` と、構成的な列挙 `legalActions`）の照合は、下の「列挙の一致」が担う。
  - 拒否の理由（`IllegalReason`）は、診断用の別の関数で作る。この関数は検証の対象外で、定理は理由に触れない。
  - 失うものもある。`Legal` 自体の誤りは、`step` との食い違いとしては現れなくなる。`legalActions` との照合と、テストで見つける。
  - `Legal` をそのまま実行すると遅い種類のフレームでは、`step` に専用の検査を書き、`Legal` との一致を証明する。どの種類がそうなっているかは、カバレッジ表に出す。
- **定理の目標**（[roadmap.md](roadmap.md) の I6）。どれも `WF s` と `CardDB.WF db` を仮定し、任意の `fuel` について述べる。

  | 名前 | 主張 |
  |---|---|
  | `step` の健全性 | `Legal db s a → ∀ e, step fuel db s a = .error e → e = .fuelExhausted`（合法手は、fuel 切れ以外の理由で失敗しない） |
  | `step` の完全性 | `(∃ r, step fuel db s a = .ok r) → Legal db s a`（合法でない手は受理されない） |
  | 列挙の一致 | `a ∈ legalActions db s ↔ Legal db s a ∧ a.actor.isPlayer`（偶然・時計・ジャッジの Action は列挙しない） |

  - 受理に `Legal` の決定手続きを使う種類のフレームでは、完全性は定義から従う。
  - 健全性は「合法な答えの適用と、その後の自動処理が、fuel 切れ以外で失敗しない」ことを言う。I4（内部エラーが起きない）と合わせて証明する。
- **I6 が保証する範囲**: I6 が言うのは、「エンジンが出した問いに対する答えの合否が、CR どおりである」ことである。`Legal` は問い（フレーム）ごとに書き、その問いを出すのは `step` だからである。次のものは I6 の対象外で、別に担保する。

  | I6 の対象外 | 担保の方法 |
  |---|---|
  | 問いが、正しい相手に正しい時点で出ること | 決定点の定理: Priority の受け渡し（I16）、`priority` の時点で盤面が `Settled` であること（I17）、任意の選択が必ず問われること（I18）。加えてシナリオテスト |
  | 決定を挟まない処理（Cleanup、誘発の検出、効果の解決）の正しさ | 手続きの定理（§8 の L2）、関係仕様（L5）、シナリオテスト、公式 FAQ の回帰 |
  | カード文面から IR への転記の正しさ | カードごとのシナリオテスト（[roadmap.md](roadmap.md) の「1 枚のカードの完了条件」） |

- **信頼する部分**（定理が正しさを保証しないもの）:
  - `Legal` の記述そのもの
  - `characteristics` と hook の導出関数（`Legal` と実装が共有する。Layers は関係仕様 L5 で別に検証する）
  - カードの IR への転記と、`custom` ハンドラ
  - 偶然・時計・ジャッジの `Action` を供給する Driver
- **`legalActions` を「候補を作って `step` で試し、通ったものを残す」形で定義してはならない。** そうすると列挙の一致の定理が無意味になる。`legalActions` は、フレームの種類ごとに候補を構成的に列挙する。
  - この形は、テストの照合先としては使ってよい。一致の証明が付くまでの間、小さな状態で `legalActions` と比べる（§11）。
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
- ObjId の付け替えを無視した状態の同値は、ループの検出器（[tournament-model.md §5](tournament-model.md#5-ループtr-505)）でも使う。同じ定義を共有する。

### 6.6 イベントの経路

盤面を変える操作は、すべて 1 つの経路 `perform` を通す（P9）。

1. **提案**: プリミティブは盤面を直接変えず、起こそうとするイベントをデータとして作る（例: 「この Unit を kill する」）。
2. **置換・防止**: 適用できる置換効果（367-375）と Prevent（438）を、イベントに適用する。同じ置換は 1 つのイベントに 1 回だけ適用する（370.2）。適用順をプレイヤーが決める場合（372）は、`choose` フレームになる。
3. **適用**: 確定したイベントを盤面に反映する。ゾーンの移動には `moveObj` を使う。
4. **発行**: 起きたイベントを記録する。誘発能力の検出（382-385）と、`step` が返す `List Event` に使う。

- 置換の段は、最初のプリミティブと同時に作る（[roadmap.md](roadmap.md) M2）。最初に入れるのは、ルール自身が持つ置換である Burn Out（432.5）だけ。カードの置換効果は M6 で足す。
- プリミティブの補題（§8 の L1）は「適用」の段に対して書く。置換の段にカードの効果が増えても、補題は書き直さずに済む。
- 置換の指示（「代わりに〜する」）は別のカードの `Effect` である。実行は作業のフレームとしてスタックに積み、`microStep` が進める（§6.1）。

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
  - `Effect.custom (id : CustomId) (args : List Arg)` は、ハンドラ表への参照と、引数の式だけを持つ。`Effect` 自体は関数を含まないので、`Repr` やカバレッジ集計が効く。
  - 引数 `Arg` は IR の式（`Amount`、`Selector`、`Condition`、変数）である。解釈器がそれを評価し、値の列をハンドラに渡す。
  - ハンドラは `CardDB` の中の表に置く。中身は「値の列を受け取り、実行すべき IR を返す関数」である。

    ```lean
    structure CustomHandler where
      expand : List Value → Effect
    ```

  - **ハンドラは `GameState` を受け取らない。** 理由は 3 つある。
    - 層の順序を守る。`CardDB` は Card 層にあり、State 層の `GameState` を参照できない（§4）。
    - 状態から読む値が、すべて IR の式として現れる。隠れ情報の扱い（§6.5）と、参照する情報の時点（359.3.f）を、解釈器の 1 か所で決められる。
    - カードのファイルは、`Riftbound.Card` だけを import すれば書ける（[card-data.md §4.1](card-data.md#41-ファイルの構成-1-弾-1-ファイル)）。
  - **展開は 1 段だけにする。** 展開結果の中に `custom` があれば、実行できない指示として飛ばす（055）。展開が必ず止まる。
  - ハンドラは、プレイ時の選択（§7.2 の「選択の宣言」）を増やせない。対象を取る効果では、対象枠をカード側の宣言に書き、選ばれた対象を引数で渡す。
  - ハンドラの結果は通常の解釈器が実行する。そのため、決定要求は通常どおり外に出る（P4）。
  - 意味の正しさ（CR とカード文面どおりか）は、そのカードのシナリオテストで担保する。
  - IR で表せない新しい仕組みが必要なら、`custom` ではなく IR にプリミティブを足す（証明を伴う）。
  - 同じ形のハンドラ（定数だけが違うもの）が 3 つを超えたら、IR の結合子かプリミティブに昇格させる。
- **解釈器は、どんな `Effect` に対しても全域にする。**
  - 未束縛の変数、未定義の `CustomId`、型の合わない値に出会った指示は、実行できない指示として飛ばす（055）。`RuleError.internal` にはしない。
  - こうすると、`WF` の保存（I3）と「内部エラーが起きない」（I4）が、ハンドラの中身によらず成り立つ。ハンドラは関数なので、「どの入力でも整った `Effect` を返す」ことは検査できない。全域にしておけば、その検査は要らない。
  - 飛ばしたことは診断用のイベントとして発行し、テストで検出する。
- **`CardDB.WF` は、判定可能な静的な条件だけにする。**
  - `CardId` が一意である。
  - 参照する Tag、Keyword、`CustomId`、トークンの定義が存在する。
  - 各カードの `Effect` で、変数が束縛されてから使われる。対象枠の番号が、宣言の範囲内にある。
  - ハンドラの結果についての条件は入れない。

### 7.2 構成要素（初期案）

| 要素 | 内容（例） |
|---|---|
| `Effect` | `seq`、`chooseOne`（宣言したモードによる分岐）、`ifThen`、`forEach`、`may`、`doThis`（Reflexive Trigger 387）、`repeat`（820）、プリミティブ、`grant`（継続効果の付与）、`delayed`（遅延能力の生成 390-393）、`custom` |
| プリミティブ | draw、discard、deal、heal、kill、banish、recall、move、ready、exhaust、stun、buff、recycle、channel、add、counter、play、hide、reveal、create、attach / detach、gainXP、score、burn、predict、prevent、replace、copy、double、swap、empower / disempower、takeControl、extraTurn、win |
| 選択の宣言 | プレイ時（355）に選ぶもの: 対象枠（Selector と数）、モード、X、任意の追加コスト。効果の本体からは番号で参照する |
| `Selector` | 種別、friendly / enemy（740.1）、場所（here、at a battlefield、in bases）、タグ、キーワード、Might の比較、数量（a / up to N / each / all）。Choose（対象を取る）は宣言した対象枠への参照、Pick（取らない）は解決時の選択として区別する（355） |
| `Amount` | 定数、for each、equal to（Might、コスト）、X |
| `Condition` | 「〜を Control しているなら」、Victory Score までの残り点、Level N、Empowered、Legion、Mighty など |
| `Trigger` | play、attack / defend、conquer / hold、move、die（Deathknell）、フェイズの開始・終了、become Mighty / Empowered、the Nth time |
| `Cost` | Energy、Power（ドメイン指定 / 任意）、exhaust、recycle、discard、味方 Unit の kill、spend XP、spend buff、disempower。追加コスト（必須 / 任意）、割引、増加（356） |
| `Duration` | this turn、this combat、while ...、until ... |
| `Ability` | passive / replacement / activated / triggered（361）と回数制限（once each turn: 371, 386） |
| `StaticMod` | Might 修正、キーワード付与、コスト修正、制限（can't ...）、許可（may play from ...）、Victory Score の修正、得点規則の修正 |

- **実装した形（2026-11-21、M3b-3）**: 上の表は初期案で、型は `Riftbound/Card/IR/` にある（[roadmap.md](roadmap.md) の M3b-3 の記録）。初期案との違いは 3 つ。
  - 再帰する型は、`List` と `Option` を自分自身の入れ子に持たない。v4.36.0 では `Option` でも入れ子の帰納型になり、`DecidableEq` を derive できないため。専用のリスト型を同じ `mutual` に置いた。
  - `Cost`（Energy と Power）は `Core.Cost` のまま。能力のコスト（Exhaust、Recycle、Discard、味方の kill など）は `AbilityCost` として別に持つ。
  - `Replace` と `Prevent` は `Effect` のコンストラクタにせず、`Ability.replacement` にした（`ReplaceEvent` と、置き換わる `EffectDef`）。
- **プレイ時の選択は、効果の本体から分けて宣言する。**
  - Spell と能力の効果は、「選択の宣言 + 本体」の組（`EffectDef`）で持つ。対象枠は宣言に並べ、本体は `.slot i` のように番号で参照する（例は [card-data.md §4.1](card-data.md#41-ファイルの構成-1-弾-1-ファイル)）。
  - 対象とモードは、コストを払う前に選ぶ（355）。宣言が本体から分かれていれば、プレイの時点で必要な選択が、`Effect` を実行せずに分かる。
  - Deflect の追加コスト（809）、対象の選び直し（750-755）、対象が不正になったときの扱い（359.3.e）も、同じ宣言を使う。
  - 対象を取らない選択（Pick）は本体に書く。解決のときに `choose` フレームになる。
  - モードごとに対象が違うカードは、モードの宣言の下に対象枠を持つ。
- 変数の束縛は、HOAS（Lean の関数）ではなく名前つき変数（`VarId`）と環境（`Env`）で表す。関数を含む帰納型では `DecidableEq` / `Repr` を導出できず、カードデータの解析もできないためである。
- `Effect` は `List Effect` を含む入れ子の帰納型になる。v4.36.0 では、この形に対して次の 2 点がある（[lean-guidelines.md §5.4](lean-guidelines.md#54-deriving-と等値性)）。
  - `deriving DecidableEq` と `induction` タクティクが使えない。
  - 同じ形の相互再帰で書いた関数と定理は通る。
- 解釈器は 1 歩の関数（`microStep`）なので、`WF` の保存は場合分けで示せる。`Effect` についての帰納法は要らない。相互再帰が要るのは、`Effect` を静的に走査する関数（等値性、変数の束縛の検査、対象枠の検査）だけである。

### 7.3 ルールの差し込み口（hook）

「Can't beats Can」（054）を実装する場所を、最初にまとめて決めておく。

- エンジンは導出関数（例: `restrictions db s`、`permissions db s`、`costMods db s`、`replacements db s ev`）を通して判定し、カード側は `StaticMod` と置換効果のデータを持つだけにする。
- 最小版（常に空リストを返すもの）を先に作る。イベントの置換（§6.6）は最初のプリミティブと同時に（[roadmap.md](roadmap.md) M2）、その他は最初にプレイを実装するマイルストーン（M4）で作る。
- hook の種類の一覧は、カードを IR に転記する試行（[roadmap.md](roadmap.md) M3b）で洗い出して確定する。最初の転記（46 枚）で、次の hook が `StaticMod` として必要になった: 誘発回数（`triggersExtra`）、ダメージの増加（`bonusDamage`）、場に出る状態（`entersReady`）、場所を限った禁止（`cantPlayer`）とキーワードの無視（`ignoreKeyword`）、勝利に必要な点（`victoryScorePlus`・`victoryScoreMinus`）。置換は `Ability.replacement`（常に有効）と `Effect.replaceNext`（1 回だけ）の 2 通り。詳しくは [ir-gaps.md](ir-gaps.md)。

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
| イベントの置換・防止 | 死ぬ代わりに Banish（Smite）、ダメージの Prevent（Ki Barrier）、Burn Out（432.5。ルール自身が持つ置換） |

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
| L1 プリミティブ | `moveObj`、イベントの「適用」の段（draw、recycle、channel、exhaust / ready） | WF の保存、物理カードの保存（`List.Perm`）、exhaust の冪等性（415.1.b） |
| L2 手続き | Cleanup、Chain、Priority / Focus、得点 | Chain は後入れ先出し（340.1）、Priority の受け渡し（312.2, 339）、`priority` の時点で盤面が `Settled`、1 人のプレイヤーは 1 つの Battlefield を 1 ターンに高々 1 回 Score する（472）、勝者の一意性 |
| L3 大域 | `Reachable` な状態の `WF`、`Legal` との一致、fuel の単調性 | §6.1、§6.3 |
| L4 効果 IR | 解釈器（`microStep`）が `WF` を保存する（したがって IR で書いた全カードが `WF` を保存する）。任意の選択が必ず問われる | プリミティブの補題からの帰結。`custom` の結果も同じ解釈器が実行するので、ハンドラの中身によらない |
| L5 関係仕様 | 実装と独立に書いた遷移の仕様との一致 | 戦闘ダメージの割り当て（467）、コスト計算（356）、Layers（478-482） |
| L6 情報 | 隠れ情報の非干渉、ObjId の付け替えを無視した状態の同値 | §6.5 |

- **`Reachable`** は帰納的に定義する。
  - 初期状態は到達可能。初期状態は、妥当な設定（`GameConfig.Valid`）と、その設定で合法なデッキから作る。
  - 到達可能な状態から、ある fuel で `step` が `.ok` を返した先も到達可能。fuel の単調性（I15）により、fuel の選び方にはよらない。
  - 大域の不変条件は、すべて「初期状態で成り立ち、`step` で保存される」の形で示す。
- **スタブに依存する証明は、具体的な実装ではなく性質に対して書く。** 後で差し替える部分は、引数として受け取る形で定理を述べる。例: 戦闘ダメージの割り当ての仕様（M5）は、`might : ObjId → Int` を引数に取る。`characteristics` を M6 で Layers に差し替えても、証明が残る。
- **得点の単調性は仮定しない。** CR は得点を失う場合を規定している（194.4.a）。

## 9. ルールとカードの版管理

- **ルール**:
  - コードに `RulesVersion` 定数（CR と TR の版の日付）を置く。
  - 規則番号の引用は常に `(CR 323.4)` / `(TR 402.1)` の形式で書く。引用はすべてその版を指す。
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
- **決定（§12 Q1）**: カードの公式文面はリポジトリにコミットする。そのうえで次を守る。
  - **免責文は必須**とする。リポジトリ直下の `README.md` に、Riot の "Legal Jibber Jabber" 方針が求める免責文を置く。
  - `NOTICE` に、カード名・カード文面・ルール文書は Riot Games の著作物で、Apache-2.0 の対象外であることを書く。
  - 非商用にする。
  - カード画像とフレーバーテキストは扱わない。
- 文面は、各カードの定義の docstring に入れる（[card-data.md §4](card-data.md#4-lean-側の表現)）。

## 11. テストと検証

- **小さな単位で進め、単位ごとに証明が通ることを確かめる。**
  - 1 単位は、1 つの定義か、1 つの定理とする。そのモジュールのビルドが通ってから、次の単位に進む。
  - 証明が通っていない定理の上に、次を積まない。`sorry` を残したまま先へ進まない。
  - Lean では、ビルドが通ることが、証明が kernel の検査を通ったことを意味する。この確認を、作業の最小の区切りにする。
- 定義と同じ単位で、`#guard` や `example : ... := by decide` による小さな検査を書く。要素が数十を超える検査は `decide +kernel` を使う（[lean-guidelines.md §5.5](lean-guidelines.md#55-decidable-と-decide)）。
- **シナリオテスト**: 状態を組み立て、Action 列を流し、結果を検査する。公式 FAQ・裁定を回帰テストにする（例: Radiance Rules FAQ の、置換効果の適用順やコスト支払いの順序）。
- **性質ベーステスト**: Plausible で「ランダムな合法手の列の後でも `WF` が成り立つ」を検査する。証明に先立って誤りを早く見つけるためである。
- **列挙の照合テスト**: 小さな状態で、`legalActions` の結果と「候補を作って `step` で試し、通ったものを残す」方法の結果を比べる。後者は定義としては禁止しているが（§6.3）、照合先としては役に立つ。列挙の一致の証明が付くまでの間の代わりにする。
- **不正な `Effect` の検出**: 解釈器が指示を飛ばしたときの診断用のイベント（§7.1）が、どのシナリオテストでも発行されないことを検査する。
- **検証はローカルで行う。** 開発者が 1 人の間は、GitHub Actions を使わない（§12 Q7）。
  - 全体の検証は、1 つのスクリプト（`scripts/verify.sh`）にまとめる。中身は、警告をエラーにしたビルド、テスト、axiom の監査、カードデータの陳腐化検査、実装カバレッジ表（カードと `Legal` の整備状況）の生成である。`sorry` は、警告をエラーにしたビルドで止まる。
  - main へマージする前に必ず通し、結果を PR の説明に書く。CI が無いので、これが検証を通した記録になる。
  - 開発者が増えたら、同じスクリプトを CI で実行する。

作業の単位と検証のコマンドは [lean-guidelines.md §7](lean-guidelines.md#7-作業の単位とローカルでの検証) に、その他の詳細は [lean-guidelines.md](lean-guidelines.md) に置く。

## 12. 決定事項（2026-11-20）

| # | 論点 | 決定 |
|---|---|---|
| Q1 | カード名・カード文面を公開リポジトリにコミットするか | **コミットする。** 1 弾 1 ファイルとし、各カードの定義の docstring に公式文面を入れる（[card-data.md §4](card-data.md#4-lean-側の表現)）。免責文は必須（§10） |
| Q2 | 初期スコープを 1v1（Duel）に絞ってよいか | **絞る。** 型と手番の走査は最初から N 人対応で作り、実装と定理は 1v1 から始める。多人数固有の規則は M9 |
| Q3 | Mathlib を依存に入れるか | **入れない**（core + Std + Plausible）。理由は、1 ファイルあたりの読み込みが重くなること、Lean の版が Mathlib に縛られること、エンジンの定義では使いにくいこと（[lean-guidelines.md §1](lean-guidelines.md#1-ツールチェーン)）。どうしても必要になったら、証明専用の別パッケージでだけ使う案を検討する |
| Q4 | Core Rules の Legacy 改訂を待つか | **待たない。** 2026-10-09 版で始め、改訂時に追従する |
| Q5 | Tournament Rules をどこまで扱うか | **Core Rules と両方に対応する。** 範囲は [tournament-model.md](tournament-model.md) のとおり（フォーマット、マッチ、時間切れ、ループ、合意の引き分け、2v2 の席順）。大会の運営・罰則は対象外 |
| Q6 | 証明を完了条件（M10）に含めるか | **含める（現状のまま）。** カタログの定理をすべて証明することと、`Legal` との一致（I6）を全フレームの種類で証明することを、M10 の完了条件に残す（[roadmap.md](roadmap.md) M10） |
| Q7 | 実装の単位と、検証を実行する場所 | **1 つの定義・1 つの定理ごとに、証明が通ることを確かめながら進める。検証はローカルで行い、GitHub Actions は使わない。** 開発者が 1 人の間の方針とする。手順は [lean-guidelines.md §7](lean-guidelines.md#7-作業の単位とローカルでの検証) |

## 13. リスクと対策

| リスク | 対策 |
|---|---|
| セットごとのルール改訂 | §9 の版管理。規則番号の引用を機械的に追えるようにする |
| `Legal` の記述量が大きくなる | フレームの種類ごとに少しずつ整備し、整備状況をカバレッジ表で見えるようにする。未整備の間はテストで担保する。受理の判定に `Legal` を使い、合法性を書く場所を 2 つに抑える（§6.3） |
| `Legal` との一致（I6）が、問いの正しさまでは保証しない | 保証の範囲を明記する（§6.3）。決定点の定理（I16〜I18）とシナリオテストで補う |
| Layers の依存関係（480-481）の実装が難しい | timestamp 順で始め、依存が必要なカードが出た時点で実装する。関係仕様（L5）で検証する |
| 効果 IR の表現力不足 | 動的な組み立ては `custom` で逃がし、頻出したら IR に昇格させる。新しい仕組みは IR のプリミティブとして足す |
| IR の形が、カードを書き始めてから変わり、証明を巻き込む | 解釈器を作る前に、意味を与えない構文だけの転記でカードを試す（[roadmap.md](roadmap.md) M3b） |
| 証明コストの膨張（Cedar の例では証明がモデルの約 3.4 倍） | 証明はプリミティブと手続きに集中させ、カード単位の証明義務をほぼゼロにする。スタブに依存する証明は性質に対して書く（§8）。置換の差し込み口を最初から用意する（§6.6） |
| 巨大な列挙型での `deriving` の性能（`LawfulBEq` の証明は構築子数の二乗で重くなり、`DecidableEq` の導出が遅いという報告もある） | カードを構築子にしない。カードはデータとして持つ |
| 入れ子の帰納型（`List Effect` を持つ `Effect`）では、v4.36.0 の `deriving DecidableEq` と `induction` タクティクが使えない（ローカルで確認） | 解釈器を 1 歩の関数にして、`Effect` についての帰納法を避ける（§7.2）。等値性は手書きするか、専用のリスト型を `mutual` で定義する。静的な走査は相互再帰で書く（[lean-guidelines.md §5.4](lean-guidelines.md#54-deriving-と等値性)） |
| CI が無いので、検証を通さないままマージしうる | マージの前に全体の検証（`scripts/verify.sh`）を通し、結果を PR の説明に書く。どのコミットも、警告をエラーにしたビルドが通る状態にする（[lean-guidelines.md §7](lean-guidelines.md#7-作業の単位とローカルでの検証)） |
| ループの検出（TR 505）に、ObjId の付け替えを無視した状態の同値が要る | 引き分けの宣言はジャッジの `Action` で受け、コアは検出しない。強制的なループの検出器は、隠れ情報（I10）と同じ同値の上に M9 で作る（[tournament-model.md §5](tournament-model.md#5-ループtr-505)） |
| 権利 | §10。免責文と NOTICE を置き、非商用にする。カード画像とフレーバーテキストは扱わない |
| 1 弾 1 ファイルのため、カードのファイルが長くなる（Origins は約 300 枚） | 長さの規約からは例外にする（[lean-guidelines.md §4.2](lean-guidelines.md#42-ファイル)）。200 枚を 1 ファイルにした試験では、ビルドは約 2 秒だった。編集時の再検査が重くなったら、弾の中でファイルを分ける |
| Tournament Rules の改訂 | Core Rules と同じ版管理（§9）で追う |
