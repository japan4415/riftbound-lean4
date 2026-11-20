# ロードマップ: 証明を積み上げる順序

[`original.md`](original.md) の「小さいところから証明を積み上げて実装を行う」を、マイルストーンの列に落とし込んだもの。全体の設計は [design.md](design.md)、ルール用語は [rules-model.md](rules-model.md) を参照。

## 進め方の原則

- **ルールの骨格を、効果を持たない（バニラの）カードで先に完成させる。** 能力システムとカード群は、その後に載せる。
- 各マイルストーンは「実装」「テスト」「証明」の 3 つを同時に満たして完了とする。証明だけ、実装だけを先行させない。
  - 後のマイルストーンで本実装に差し替える仮の実装（スタブ）は、そう明記する。
- 証明は下の層から積む: データ（L0）→ プリミティブ（L1）→ 手続き（L2）→ 大域（L3）→ 効果 IR（L4）→ 関係仕様（L5）→ 情報（L6）。
  - 層の定義は [design.md §8](design.md#8-証明を積み上げる方針) を参照。
  - L4（解釈器の `WF` 保存）は、解釈器を作る M4 から始め、プリミティブを足すたびに広げる。
- 合法性の仕様 `Legal` と、それとの一致（I6）は、決定のフレームの種類ごとに、そのフレームを作るマイルストーンで整備する。
- 規則番号は CR 2026-10-09 版のもの。

## 不変条件・定理のカタログ

| ID | 内容 | 層 | 初出 |
|---|---|---|---|
| I1 | **物理カードの保存**: セットアップ後、全ゾーンにある PhysId の列は、`step` の前後で互いに並べ替え（`List.Perm`）の関係にある。トークンは PhysId を持たないので影響しない | L1 | M2 |
| I2 | **位置の一意性**: 各 ObjId はちょうど 1 つのゾーンにある（ゾーン列の連結が `Nodup`） | L1 | M2 |
| I3 | **整形性の保存**: 初期状態は `WF`。`WF s` かつ `step cfg db s a = .ok (s', es)` なら `WF s'`。したがって `Reachable s → WF s` | L3 | M2（以後、マイルストーンごとに対象の遷移を広げる） |
| I4 | **内部エラーが起きない**: `WF s` なら、`step` は `RuleError.internal` を返さない | L3 | M2〜 |
| I5 | **進行性**: ゲームが終わっていなければ、投了以外の合法手があるか、偶然の決定が求められている | L3 | M3 |
| I6 | **`Legal` との一致**: `step` の健全性・完全性と、`legalActions` の列挙の一致（[design.md §6.3](design.md#63-できること全ての担保)） | L3 | M2（マリガンと偶然の決定）から、フレームの種類ごとに |
| I7 | **勝者の一意性**: 1v1 では勝者は高々 1 人（323.1 の「全対戦相手より多い」） | L2 | M5 |
| I8 | **資源の会計**: Rune Pool は負にならない。Channel と Recycle の間で Rune の総数が保存される | L1 | M3 |
| I9 | **ターン構造**: フェイズの順序が固定されている。Chain は後入れ先出し（340.1）。Discretionary Action は Priority を持つプレイヤーだけが行える（312.1） | L2 | M3〜M4 |
| I10 | **隠れ情報の非干渉**: プレイヤー p の合法手は `view p s` にだけ依存する（偶然の決定を除く。ObjId の付け替えに対して不変な形で述べる） | L6 | M9 |
| I11 | **Score の回数制限**: 1 人のプレイヤー（2v2 ではチーム）は、1 つの Battlefield を 1 ターンに高々 1 回 Score する（472, 491.8.b） | L2 | M5 |
| I12 | **自動処理の停止**: Cleanup の反復・Expiration のループ・Layers の反復が有限回で止まる。言えない部分は、fuel で扱っていることを明記する | L2 | M5〜 |

**得点の単調性は入れない。** CR は得点を失う場合を規定している（194.4.a）。

---

## M0: 基盤整備

**実装**
- `lean-toolchain`（`leanprover/lean4:v4.36.0`）と `lakefile.toml` を置く。設定は [lean-guidelines.md](lean-guidelines.md) に従う。
- ライブラリの骨組みを作る: `Riftbound`、`RiftboundCards`、`RiftboundDriver`、`RiftboundTest`（test driver）。全ファイルを `module` にする。
- GitHub Actions を置く: `leanprover/lean-action@v1` で build・test・axiom 監査を行い、`--wfail` を付ける。
- `sorry` の検出と、docstring 中の CR 引用を抽出するスクリプト（のちのカバレッジ集計用）を作る。
- リポジトリ直下の `README.md` に免責文を置く（[design.md §10](design.md#10-カードデータと権利)）。
- **技術的な確認（スパイク）**:
  - `lake lint` の組み込み linter の設定
  - lean-action の入力（`axiom-audit` など）
  - lean-beam と module system の併用
  - 数百件の `CardDef` に対する検査を `decide` でするか `#guard` でするか

**完了条件**: CI が通る。`lake build` と `lake test` が通る。

## M1: 静的データとデッキ構築（CR 101-103, 125-187）

**実装**
- `Domain`（134）、`CardType` / Supertype / Tag（133）、`Keyword` と `KeywordInst`（28 種、805-832）を定義する。
- `Cost`（Energy と、ドメイン別 / 任意の Power: 131, 135.2.e）と Might（143）を定義する。
- `CardDef` と `CardDB` を作る。この段階ではメタデータだけで、能力は空。テスト用にバニラカードを数枚置く。
- `Mode` の最小版を作る: 1v1 Duel のみで、Victory Score 8、Battlefield 2 枚（487）。他のモードは M9 で足す。
- デッキ構築の合法性 `DeckValid mode deck` を、判定可能な述語として定義する。対象:
  - Champion Legend 1 枚（103.2）
  - Chosen Champion（Champion Tag が一致し、Signature ではない: 103.3.a）
  - Main Deck 40 枚以上（103.3）
  - 同名 3 枚まで（Chosen Champion も数える: 103.3.b）
  - Signature 合計 3 枚まで、すべて同じ Champion Tag（103.3.d）
  - Domain Identity（103.2.b）
  - Rune Deck 12 枚（103.4）
  - Battlefield の枚数と、2 枚以上必要なときの同名禁止（103.5）

**証明（L0）**
- `Decidable DeckValid`。Bool による判定と `Prop` の仕様が一致すること（`deckValid_iff`）。
- `Cost` の算術。割引の後も Energy と Power は 0 未満にならない（356.6）。

このマイルストーンはゲーム進行から独立しているので、最初の証明の練習台にちょうどよい。

## M2: ゾーン・オブジェクト・セットアップ・エンジンの骨格（CR 105-124, 110-118, 414, 417, 431, 432）

**実装**
- `PlayerId` / `PhysId` / `ObjId` / `CardId` / `Timestamp` を定義する。
- ゲームオブジェクト（種別: カード / トークン / Chain 上の能力）、ゾーン（エンジン内部用の `setAside` を含む）、`GameState`、`WF` を定義する。
- 唯一のゾーン移動プリミティブ `moveObj` を作る。Non-Board ゾーンを出入りしたら、新しい ObjId を払い出す（124）。
- Draw（414）、Recycle（417）、Channel（431）、Burn Out（432）を作る。
  - **スタブ**: Burn Out はこの時点では手続きとして直接実装する。置換効果としての振る舞い（432.5）は M6 で置換の枠組みに載せ替える。
- **エンジンの骨格を作る**: フレーム（`choose` のうちマリガン、`chance`）、`Action`（行為者 + 内容）、`step`（fuel つき）、`legalActions`、`Legal` の最初の版。
- セットアップ（110-118）を `step` で進める:
  - Legend と Chosen Champion の配置
  - Battlefield の用意（113）。Duel では各自 3 枚から 1 枚をランダムに選ぶ（487.5）
  - シャッフル、手番順、4 枚引く、マリガン（脇に置く → 引く → Recycle）
- `RiftboundDriver` の最小版を作る: seed つき乱数で偶然の決定に答える。

**証明（L1〜L3）**
- I1、I2。`moveObj`・Draw・Recycle・Channel の各プリミティブが `WF` を保存すること。
- セットアップの遷移について I3 と I4。
- マリガンと偶然の決定について I6（`Legal` との一致。偶然の決定の `Legal` は `List.Perm`）。
- Main Deck が空でなければ、draw で手札が 1 増え、Main Deck が 1 減る。空なら Burn Out を経由する（315.4.b）。
- Burn Out では、ちょうど 1 人の対戦相手が 1 点を得る（432.2.c）。
- Non-Board ゾーンを経由した後の ObjId は、どの既存 ObjId とも異なる（124）。
- セットアップ直後の各手札が 4 枚である。

## M3: ターン骨格と資源（CR 301-317, 160-168, 430, 445, 649-651, 734-738）

**実装**
- フェイズを順に作る。
  - Awaken: Control するものをすべて Ready（315.1）
  - Beginning Step と Scoring Step。**スタブ**: Battlefield を Control する手段は M5 で入るので、それまで Hold（315.2.b）は何もしない。
  - Channel: 2 枚。Duel の後手は最初の 1 回だけ 1 枚多い（487.7）
  - Draw: 1 枚
  - Main
  - Ending / Expiration: Heal、「このターン」効果の失効、Rune Pool を空にする（317.2）
- Rune Pool と、Basic Rune の 2 つの Add 能力（164.2）、Pay（445）を作る。
  - **スタブ**: Add 能力は即座に解決する。Chain に Pending として載り、即座に finalize・解決する振る舞い（430.2）は、M4 で Chain を作るときに入れる。
- `priority` フレーム: Pass、ターン終了。
- 投了（649-651。2 人の場合は残った 1 人が勝つ: 651.1）。
- ターンの受け渡しと追加ターン（734-738）。
- `#eval` で、両者が何もせずにパスし続ける対局が回ることを確認する。

**証明（L1〜L3）**
- I5、I8。I9 のうちフェイズの順序。
- `priority` フレームと投了について I6。
- Main Phase の開始時に Rune Pool が空になる（167）。
- Channel は失敗しない（Rune が足りなければ出せるだけ: 431.3）。
- Exhaust の冪等性（415.1.b）、Unit の Ready の冪等性（416.1.b）。
- 1v1 では Turn Player が交互に入れ替わる（追加ターンが無い場合）。
- 各フェイズの処理について I3 と I4。

## M4: カードのプレイ・Chain・効果 IR v0（CR 325-340, 349-359, 399-407, 426, 430.2）

**実装**
- プレイ手順の 6 段階（354-359）。
  - 総コストの決定（356）、支払い（357）。
  - 合法性の確認（358）。失敗したら、フレームに保存したスナップショットに巻き戻す。
- HOT FEPR（334-340）、Priority / Focus（311-313）。
- Add 能力を、Chain 経由で即座に finalize・解決する形にする（430.2）。
- タイミングの許可（Action 806、Reaction 813）。
- Unit・Gear は finalize 直後に即解決する（337.2）。
- Counter（426）、対象が不正になったときの処理（359.3.e。Ignored と Negated の区別を含む）。
- **hook の最小版**: `restrictions`、`permissions`、`costMods` は常に空を返す（[design.md §7.3](design.md#73-ルールの差し込み口hook)）。
- **効果 IR v0**（draw、deal、kill、buff、ready、exhaust、stun、recall、banish）、Selector v0、決定要求で中断・再開できる解釈器。
- 単純な呪文と、バニラの Unit・Gear を使えるようにする。

**証明（L2〜L4）**
- I9（Chain は後入れ先出し、Discretionary Action は Priority を持つプレイヤーだけ）。
- プレイ・対象・コストのフレームについて I6。
- **L4 の開始**: IR v0 の各プリミティブと解釈器が `WF` を保存する（I3 を効果の解決に広げる）。
- 合法性の確認に失敗したら、盤面がプレイ開始時のスナップショットと一致する（358.5 のモデル化）。

## M5: 移動・Showdown・戦闘・得点・Cleanup（CR 144, 190, 318-324, 341-348, 447-474）

**実装**
- Standard Move（144）、Contested（190.3）。
- Cleanup の 10 ステップ（323）。Showdown / Combat の Staged 化。
- Showdown（344-348）。
- Combat の 3 ステップ（466-468）。
  - ダメージの割り当て（467.2.c）。
  - 戦闘結果と Recall。
- **戦闘に必要なキーワードの意味は、ここで一本化して実装する**: Tank（815）、Assault（807）、Shield（814）、Ganking（810）、Stun（424）。
  - Backline（826）は Unleashed で入るので M8b で足す。割り当ての実装は、それを足せる形にしておく。
- **スタブ**: 実効特性（`characteristics`）は「印刷値 + カウンター + 保存された期間つきの Might 修正」の暫定版にする。完全な Layers は M6 で差し替える。
- Conquer と Hold（Scoring Step のスタブを実体化する）、Final Point（473.1.b）、勝利（323.1）。
- **バニラのデッキ同士で、1v1 が最初から最後まで遊べる状態にする。**

**証明（L2〜L5）**
- I7、I11、I12（できる範囲で）。
- **最初の関係仕様（L5）**: 戦闘ダメージの割り当て（467.2.c）を、実装と独立した `Prop` として書き、実装がそれを満たすことを示す。
- 得点が 0 のときに得点を失う指示は何も起こさない（194.4.a）。
- 移動・戦闘のフレームについて I6。

## M6: 能力システムと Layers（CR 360-398, 475-482, 805-817）

**実装**
- Passive（363-366）。
- Replacement（367-375）: 適用順は 372、1 つのイベントに同じ置換は 1 回まで（370.2）。Burn Out をここで置換効果に載せ替える（432.5）。
- Triggered（382-385）: 同時に誘発したものの順序（383.3.d）と、戦闘開始時の例外（466.2.d.1）。
- Reflexive、Delayed、Linked（387-398）。
- **Layers**: Copy → Trait → Ability → Arithmetic（479）。変化がなくなるまでの反復（478.2-478.3）。同一層内は timestamp 順（482）。M5 の暫定版を差し替える。依存関係（480-481）は、それが必要なカードが来た時点で入れる。
- hook を `StaticMod` で埋める（[design.md §7.3](design.md#73-ルールの差し込み口hook)）。
- 残りの Origins 期のキーワード: Accelerate、Deathknell、Deflect、Hidden、Legion、Temporary、Vision。
  - Action と Reaction は M4、戦闘のものは M5 で実装済み。

**証明**
- 置換効果は、1 つのイベントに対して同じものが高々 1 回しか適用されない（370.2）。
- キーワードの意味の補題。例: Assault X は Attacker である間だけ Might を X 増やす（807）。
- Arithmetic 層では、増加が減少より先に適用される（479.4.e）。
- 能力系のフレーム（誘発の順序、置換の順序）について I6。

## M7: カードの取り込みと、Origins・Proving Grounds の全カード

**着手条件**: カードの文面をリポジトリにどう置くか（[design.md §12](design.md#12-未決事項ユーザーの判断が要るもの) Q1）が決まっていること。

**実装**
1. **棚卸し**: Origins と Proving Grounds の全カードが要求するプリミティブ・結合子・hook を洗い出す。不足分（Discard、Reveal、Double、Swap、Detach、Prevent など）を IR に足す。
2. [card-data.md](card-data.md) のパイプライン: 取得 → 正規化 → `Meta.lean` の生成。実装カバレッジ表、`custom` のハンドラ表。
3. Origins（通し番号上 298 種）と Proving Grounds（24 種）の効果を IR で書く。
4. 公式 FAQ の裁定を回帰テストにする。

**証明（L4）**
- 新しく足したプリミティブについて、`WF` 保存の補題を足す（L4 を広げる）。
- 具体的な `CardDB` が `CardDB.WF` を満たすことを検査する（参照する Tag・Keyword・custom ハンドラが定義済みであることなど）。

## M8: 後続セット（セットごとの小マイルストーン）

各セットで「棚卸し → 新しいキーワード・プリミティブ・hook → カード → テスト」の順に進める。手順は [card-data.md](card-data.md) に従う。

| 小マイルストーン | 追加する仕組み（CR） |
|---|---|
| M8a Spiritforged | Attach / Equipment（716-719, 150）、Equip、Quick-Draw、Repeat、Weaponmaster、Unique（825。Spiritforged のカードに既に現れる）、Gold トークン |
| M8b Unleashed | XP / Level / Hunt（728-733, 823-824）、Ambush、Backline、Predict、Replace / Create（439-440）、Battlefield トークン |
| M8c Vendetta | Empower / Empowered / Flow / Burn（827-829, 441-443）、複数の型を持つカード（177-178）、Skip（444） |
| M8d Radiance | Deploy、Disarm、Show Off（830-832）、Copy 層（479.1）、Pick と Choose の区別、構築時の追加選択（103.1） |
| M8e Legacy（2027-01） | ルールの全面改番への追従、新しいカード文面のテンプレート |

## M9: 多人数戦と隠れ情報（CR 483-491, 651-652, 128）

**実装**
- FFA3 / FFA4 / 2v2（489-491）。
- 多人数の移動先の制限（144.4.a.1, 449.2, 464）。
- 投了による除去（投了後に 2 人以上が残る場合: 651.2, 652。2v2 ではチーム全員が敗北: 651.4）。
- 2v2 固有の規則（得点の共有、味方の招待、Final Point の調整など: 491.8）。
- `view` を完成させる。
- M8 までに `partial`（多人数の仕組み待ち）としたカードを `full` にする。

**証明（L6）**: I10。

## M10: 完了判定（original.md の最終目的）

次をすべて満たしたとき、その時点のカードプールについて R5（[design.md §1](design.md#1-要求の整理)）を達成したとみなす。

1. 公開済みの全セットで、全カードの `ImplStatus` が `full` である。
2. `custom` ハンドラの一覧があり、それぞれにシナリオテストがある。
3. `Legal` が全フレームの種類を覆い、全種類について I6 が証明されている。
4. I1〜I12 が証明されている。I12 のうち fuel で扱う部分は、その範囲を明記している。
5. CI のすべての検査（build、test、axiom 監査、カードデータの陳腐化検査）が通る。

以後は継続作業になる: 新しいセットの追加（M8 と同じ手順）、関係仕様（L5）の拡充（コスト計算 356、Layers 478-482）、性能改善、CLI。

---

## 実装状況（ImplStatus）の定義

- `todo`: メタデータのみ。
- `partial`: 一部が未実装。理由を docstring に書く（例: 多人数の仕組みを待っている場合は `needs-M9`）。
- `full`: その時点で実装済みのモードすべてで、カードの文面どおりに動く。

## 1 枚のカードの完了条件

1. メタデータが生成済みである（`Meta.lean`）。
2. 効果が IR で書かれている。`custom` を使う場合は、ハンドラにシナリオテストがある。
3. 実装状況が `full` である。
4. シナリオテストが 1 つ以上ある。
5. 公式 FAQ・エラッタがあれば、それを反映した回帰テストがある。

**キーワードだけのカード**（効果の文が無いもの）は、2 と 4 を免除する。持っているキーワードすべてに意味の補題とテストがあれば、生成だけで `full` にしてよい。
