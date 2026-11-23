# ロードマップ: 証明を積み上げる順序

[`original.md`](original.md) の「小さいところから証明を積み上げて実装を行う」を、マイルストーンの列に落とし込んだもの。全体の設計は [design.md](design.md)、ルール用語は [rules-model.md](rules-model.md) を参照。

## 進め方の原則

- **小さな単位で進め、単位ごとに証明が通ることを確かめる。** 1 単位は、1 つの定義か、1 つの定理とする。ビルドが通ってから次へ進み、証明が通っていない定理の上に次を積まない。検証はローカルで行う（[lean-guidelines.md §7](lean-guidelines.md#7-作業の単位とローカルでの検証)、[design.md §12](design.md#12-決定事項2026-11-20) Q7）。
- **ルールの骨格を、効果を持たない（バニラの）カードで先に完成させる。** 能力システムとカード群は、その後に載せる。
- 各マイルストーンは「実装」「テスト」「証明」の 3 つを同時に満たして完了とする。証明だけ、実装だけを先行させない。
  - 後のマイルストーンで本実装に差し替える仮の実装（スタブ）は、そう明記する。
- 証明は下の層から積む: データ（L0）→ プリミティブ（L1）→ 手続き（L2）→ 大域（L3）→ 効果 IR（L4）→ 関係仕様（L5）→ 情報（L6）。
  - 層の定義は [design.md §8](design.md#8-証明を積み上げる方針) を参照。
  - L4（解釈器の `WF` 保存）は、解釈器を作る M4 から始め、プリミティブを足すたびに広げる。
- 合法性の仕様 `Legal` と、それとの一致（I6）は、決定のフレームの種類ごとに、そのフレームを作るマイルストーンで整備する。
- **後で差し替える部分に、証明を縛り付けない。**
  - 差し込み口は、空の実装で先に作る。イベントの置換の段は M2 で、その他の hook は M4 で作る（[design.md §6.6](design.md#66-イベントの経路)、[§7.3](design.md#73-ルールの差し込み口hook)）。
  - スタブに依存する証明は、具体的な実装ではなく性質に対して書く（[design.md §8](design.md#8-証明を積み上げる方針)）。
- **IR の形は、解釈器と証明を作る前に、実際のカードで確かめる**（M3b）。
- 規則番号は CR 2026-10-09 版と TR 2026-10-09 版のもの。

## 不変条件・定理のカタログ

| ID | 内容 | 層 | 初出 |
|---|---|---|---|
| I1 | **物理カードの保存**: セットアップ後、全ゾーン（エンジン内部用の `setAside` と `outOfGame` を含む）にある PhysId の列は、`step` の前後で互いに並べ替え（`List.Perm`）の関係にある。トークンは PhysId を持たないので影響しない | L1 | M2 |
| I2 | **位置の一意性**: 各 ObjId はちょうど 1 つのゾーンにある（ゾーン列の連結が `Nodup`） | L1 | M2 |
| I3 | **整形性の保存**: 初期状態は `WF`。`WF s` かつ `step fuel db s a = .ok (s', es)` なら `WF s'`。したがって `Reachable s → WF s`。`WF` は構造の条件だけを含む（[design.md §5.2](design.md#52-ゾーンとオブジェクト)） | L3 | M2（以後、マイルストーンごとに対象の遷移を広げる） |
| I4 | **内部エラーが起きない**: `WF s` かつ `OwnerOk s`（と、カードを使うようになってからは `CardDB.WF db`）なら、`step` は `RuleError.internal` を返さない。`custom` ハンドラの中身にはよらない（解釈器が全域なので）。M2c で証明（`step_not_internal`、到達可能な状態では `Reachable.not_internal`） | L3 | M2〜 |
| I5 | **進行性**: ゲームが終わっていなければ、投了以外の合法手があるか、偶然の決定が求められている。分割した決定の途中でも行き止まりにならない。M3 で証明（`Reachable.progress`。`Reachable.exists_legal` が、偶然の決定を含めて合法な答えの存在を述べる） | L3 | M3 |
| I6 | **`Legal` との一致**: `step` の健全性・完全性と、`legalActions` の列挙の一致（[design.md §6.3](design.md#63-できること全ての担保)）。M2 のフレーム（偶然の決定、マリガン、Burn Out）については、完全性（`legal_of_step_ok`）、健全性（`step_sound`）、列挙の一致（`legalActions_iff`）がすべて証明済み | L3 | M2（マリガンと偶然の決定）から、フレームの種類ごとに |
| I7 | **勝者の一意性**: 1v1 では勝者は高々 1 人で、引き分けなら 0 人（CR 323.1 の「全対戦相手より多い」）。M5a で証明（`win_condition_unique`、`winner_spec`） | L2 | M5 |
| I8 | **資源の会計**: Rune Pool は負にならない。Channel と Recycle の間で Rune の総数が保存される。M3 後半で証明（`RunePool.total_spend`、`applyRune_adds_one`、`applyRune_recycle_zones`、`channelOne_zones`） | L1 | M3 |
| I9 | **ターン構造**: フェイズの順序が固定されている（M3 前半で証明: `turnPhases_chain`、`microStep_phase`）。Chain は後入れ先出し（340.1。M6a で証明: `applyActivate_chain`・`applyCast_chain`・`resolveFrames_top`・`finishItem_top_chain`）。Discretionary Action は Priority を持つプレイヤーだけが行える（312.1） | L2 | M3〜M6a |
| I10 | **隠れ情報の非干渉**: プレイヤー p の合法手は `view p s` にだけ依存する（偶然の決定を除く。ObjId の付け替えに対して不変な形で述べる） | L6 | M9 |
| I11 | **Score の回数制限**: 1 人のプレイヤー（2v2 ではチーム）は、1 つの Battlefield を 1 ターンに高々 1 回 Score する（472, 491.8.b）。M5a で、1 つの Battlefield について証明（`scoreBf_twice`）。2v2 のチーム単位は M9 | L2 | M5 |
| I12 | **自動処理の停止**: 到達可能な状態では、Cleanup の反復・Expiration のループ・効果の解決が、有限の歩数で次の決定点に達する（ある fuel で `step` が fuel 切れにならない）。言えない部分は、fuel で扱っていることを明記する。Layers の反復は、内側の上限で必ず止まる（[design.md §5.4](design.md#54-特性の導出layers)）。**調査の結果と単位の分け方は [termination.md](termination.md)。I12a（Cleanup）は証明済み、残りは未** | L2 | M5〜 |
| I13 | **大会のデッキと Core Rules のデッキ**: Constructed で合法なデッキからサイドボードを除いたものは、Battlefield を 3 枚求めるモード（1v1 Duel など）の Core Rules のデッキ構築でも合法である（TR 402.1, 601 と CR 103）。Battlefield の枚数はモードが決めるので（CR 103.5）、モードを限定して述べる | L0 | M1 |
| I14 | **時間切れ後の終了**: 時計が時間切れを知らせた後、ゲームは有限のターン数で終わる（追加 3 ターンの後に点差で決まる: TR 408.2） 。局所の事実（`three_more_turns`、`beginTurn_ends`、`beginTurn_next`）に、**全体**（`Reachable.clockOk`、`step_keep`、`time_called_bound`）を足して**証明済み** | L2 | M5b |
| I15 | **fuel の単調性**: `step n db s a = .ok r` かつ `n ≤ m` なら、`step m db s a = .ok r`。fuel 切れ以外のエラーも、fuel によらない | L3 | M2 |
| I16 | **Priority の受け渡し**: Closed でプレイヤーがパスしたら、次の `priority` フレームは手番順で次のプレイヤーのものになる。全員が続けてパスしたら、最も新しい Finalized の項目が解決される（312.2, 339, 340） | L2 | M4 |
| I17 | **`priority` の時点で `Settled`**: `priority` フレームが先頭にある到達可能な状態は、`Settled` である（Cleanup が不動点に達している: 322-323）。M5a では局所版だけ証明（`cleanupFrame_pop_settled`、`Settled.no_lethal`）。全体の形は未 | L2 | M5 |
| I18 | **任意の選択は必ず問われる**: 解釈器は、`may`、任意の追加コスト、Pick を自分では決めない。必ず `choose` フレームを出す（[design.md §3](design.md#3-設計原則) の P4） | L4 | M4 |
| I19 | **ループの検出の健全性**: 検出器が強制的なループを報告したら、その後も強制的な答えだけで、同値な状態に戻り続ける（[tournament-model.md §5](tournament-model.md#5-ループtr-505)） | L3 | M9 |

I16〜I18 は、`Legal` との一致（I6）が保証しない「問いの正しさ」を補う定理である（[design.md §6.3](design.md#63-できること全ての担保)）。

**得点の単調性は入れない。** CR は得点を失う場合を規定している（194.4.a）。

---

## M0: 基盤整備

**実装**
- `lean-toolchain`（`leanprover/lean4:v4.36.0`）と `lakefile.toml` を置く。設定は [lean-guidelines.md](lean-guidelines.md) に従う。
- ライブラリの骨組みを作る: `Riftbound`、`RiftboundCards`、`RiftboundDriver`、`RiftboundTest`（test driver）。全ファイルを `module` にする。
- 全体の検証スクリプト `scripts/verify.sh` を作る: 全ライブラリのビルド（`--wfail`）、`lake test`、axiom の監査（`lake check --inadvisably-no-sandbox`）。`sorry` は `--wfail` で止まる。GitHub Actions は置かない（[lean-guidelines.md §7](lean-guidelines.md#7-作業の単位とローカルでの検証)）。
- docstring 中の CR 引用を抽出するスクリプト（のちのカバレッジ集計用）を作り、`verify.sh` から呼ぶ。
- リポジトリ直下の `README.md` に免責文を置き、`NOTICE` にカード由来のデータの権利を書く（[design.md §10](design.md#10-カードデータと権利)）。2026-11-20 に設置済み。
- **技術的な確認（スパイク）**: 2026-11-20 に済み。結果は [lean-guidelines.md](lean-guidelines.md) に [確認済] として書いた。
  - `lake lint`: 環境 linter が無いので使わない。構文系の linter は `--wfail` で足りる（§2）
  - `lake check --inadvisably-no-sandbox`: `defaultTargets` の `Riftbound` だけを監査する。`RiftboundDriver` の `native_decide` は対象外で、コアの `native_decide` は拒否される（§7.2）
  - lean-beam と module system: 併用できる。module の中の `#guard` には `meta import` が要る（§3、§8）
  - 数百件の `CardDef` の検査: `decide +kernel` で定理にでき、`#guard` なら約 0.2 秒。素の `decide` は使えない（§5.5）
  - `Std.ExtTreeMap` を持つ状態: 素の `decide` は 20 個で失敗し、`decide +kernel` は 100 個で約 0.5 秒（§5.3）

**完了条件**: `scripts/verify.sh` がローカルで通る（`lake build`、`lake test`、axiom の監査）。2026-11-20 に達成した。

## M1: 静的データとデッキ構築（CR 101-103, 125-187）

**実装**
- `Domain`（134）、`CardType` / Supertype / Tag（133）、`Keyword` と `KeywordInst`（28 種、805-832）を定義する。
- `Cost`（Energy と、ドメイン別 / 任意の Power: 131, 135.2.e）と Might（143）を定義する。
- `CardDef` と `CardDB` を作る。この段階ではメタデータだけで、能力は空。テスト用にバニラカードを数枚置く。
- `Mode` の最小版を作る: 1v1 Duel のみで、Victory Score 8、Battlefield 2 枚（487）。他のモードは M9 で足す。`Mode` のデータ部分は `Core` に置く（`GameConfig` とデッキ構築の両方が参照する）。
- デッキ構築の合法性 `DeckValid mode deck` を、判定可能な述語として定義する。対象:
  - Champion Legend 1 枚（103.2）
  - Chosen Champion（Champion Tag が一致し、Signature ではない: 103.3.a）
  - Main Deck 40 枚以上（103.3）
  - 同名 3 枚まで（Chosen Champion も数える: 103.3.b）
  - Signature 合計 3 枚まで、すべて同じ Champion Tag（103.3.d）
  - Domain Identity（103.2.b）
  - Rune Deck 12 枚（103.4）
  - Battlefield の枚数と、2 枚以上必要なときの同名禁止（103.5）
- `Format`（Constructed / Sealed / Draft）と、フォーマットごとのデッキの合法性を作る（[tournament-model.md §2](tournament-model.md#2-フォーマットとデッキの合法性)）。
  - `ConstructedDeckValid`: Main Deck ちょうど 40 枚、名前の異なる Battlefield 3 枚、サイドボード 10 枚以下、セットの合法性と禁止カード（TR 402, 403, 601）
  - `SealedDeckValid` / `DraftDeckValid`: 25 枚 / 20 枚以上、任意の 3 ドメイン、枚数制限なし（TR 602）

**証明（L0）**
- `Decidable DeckValid`。Bool による判定と `Prop` の仕様が一致すること（`deckValid_iff`）。フォーマットごとの述語も同様。
- I13（Constructed で合法なら、Battlefield を 3 枚求めるモードの Core Rules でも合法）。
- `Cost` の算術。割引の後も Energy と Power は 0 未満にならない（356.6）。

このマイルストーンはゲーム進行から独立しているので、最初の証明の練習台にちょうどよい。

**実装の記録（2026-11-20）**
- 実装したファイル: `Core/{Ids,Domain,CardType,Cost,Might,Keyword,Mode}.lean`、`Card/{CardDef,CardDB}.lean`、`Rules/Deck.lean`、`Tournament/{Format,DeckLegality}.lean`。テストは `RiftboundTest/{Core,Deck,Tournament,Fixtures}.lean`。
- **`deckValid_iff` は作らなかった。** `DeckValid` の各規則を `Decidable` なモジュール化された述語として書き、判定は `decide` が行う。手書きの Bool の検査をもう 1 つ持つと、両者を揃える作業が増え、一致の定理は自明に近くなるため。述語の正しさは、規則ごとに 1 点だけ壊したデッキのテストで確かめる（`RiftboundTest/Deck.lean`、`Tournament.lean`）。
- `CardDef` に `sets : List SetCode` を足した（TR 601.2 の「合法なセットで印刷されたか」の判定に要る）。
- 実装状況の `partial` は予約語なので、コンストラクタは `«partial»` と書く。
- Sealed と Draft の合法性は、tournament-model.md §7 の項目 8〜9 のとおり簡略にした。
- I13 は `constructedDeckValid_deckValid`（`Tournament/DeckLegality.lean`）。Battlefield を 3 枚求めるモードで述べる。

## M2: ゾーン・オブジェクト・セットアップ・エンジンの骨格（CR 105-124, 110-118, 414, 417, 431, 432）

**M2 は 2 つに分けて進める。** M2a（状態・ゾーン・`moveObj`・プリミティブとその証明）を先に作り、M2b（エンジンの骨格・セットアップ・Driver）をその上に作る。以下の項目のうち、M2a が済んだものには「（M2a 済）」を付けた。

### M2d の実装の記録（2026-11-20）: セットアップ後の手札は 4 枚

- 定理 **`Reachable.opening_hands`**: セットアップが終わった（`pending` が空の）到達可能な状態では、**どのプレイヤーの手札もちょうど 4 枚**（CR 116, 117）。どう答えたかによらない（マリガンで何枚脇に置いても、同じ枚数を引くので 4 枚）。
- 証明は不変条件 `HandInv`（`Invariant/Hands.lean`）。各プレイヤーについて「手札の枚数 + スタックがこれから手札に入れる分 = 4」を、すべての `step` で保つ。「スタックが入れる分」は、手番順のフレーム（4）、`setupHands`（4）、`draw p n`（n）、`mulligan p k`（k: 脇に置いた k 枚はマリガンが終わると引き直される）。手番順は `setupHands` が積まれる時点で決まっている（`HandInv.turn`）。
- そのためにエンジンを少し変えた: **手番順の答えが `setupHands` フレームを積む**（以前は初期のスタックに入っていた）。`setupHands` が実行されるとき手番順が決まっていることが、構造から明らかになる。
- 補助の定理: `drawOne_hand`、`mulliganPick_hand`、`battlefield_hands`、`recycleAll_hands`（ドロー・マリガン・Recycle・Battlefield の選択が、他のプレイヤーの手札を変えない）、`moveObj_zone_unchanged`、`applyAction_handInv`、`microStep_handInv`、`advance_handInv`、`step_handInv`、`GameState.initial_handInv`。`MoveSpec` に `turnOrder` と `pending` が変わらないことを足した。
- これで M2 で残していた「セットアップ後の手札が 4 枚」は、テストだけでなく定理になった。残るのは、一般の置換効果の枠組み（M6）。

### M2c の実装の記録（2026-11-20）: I4 と健全性

M2b で残した 3 点のうち、1 と 2 を済ませた。

- **フレームの再設計。** 健全性の証明に、フレームが「盤面の古い写し」を持たないことが要る。そこでフレームから盤面のデータを除いた（design.md §6.2）。`mulligan p n` は選んだ枚数だけを持ち、選んだカードはその場で `setAside` に移す。`chanceRecycle p` と `chanceBurnOut p` は、脇に置いたカードと Trash の全体を並べ替える。`chooseBurnOut p` は相手だけを選ぶ。Burn Out の順序は CR 432.2 の文面どおり（Trash を山札に戻す → 相手を選んで点を与える）。
- **所有者の不変条件 `OwnerOk`**（CR 056）。Non-Board ゾーンのカードの Owner は、そのゾーンの持ち主。`WF` とは別の述語にした。`moveObj`、並べ替え、Recycle、ドロー、オブジェクトの追加、初期状態、`step` が保つ（`moveObj_ownerOk`、`step_ownerOk`、`GameState.initial_ownerOk`）。`addObject` は、行き先がその Owner のゾーンでないと失敗する。
- 証明した定理: `moveObj_isSome`（移動が成功する条件）、`recycleAll_some`、`applyAction_isSome`（合法な答えは `applyAction` が必ず適用できる）、`advance_error`（作業の失敗は fuel 切れだけ）、**`step_sound`**（合法な答えは fuel 切れ以外で拒否されない。I6 の健全性）、**`step_not_internal`**（**I4**）、`Reachable`、`Reachable.inv`（到達可能な状態は `WF` と `OwnerOk`）、`Reachable.not_internal`、`drawOne_lengths_of_ownerOk`（ドローで山札 −1、手札 +1。所有者の仮定が要らなくなった）。
- テスト: マリガンで 2 枚を脇に置き、2 枚引き、2 枚が山札の下に戻ること。Burn Out の一連の流れ（空の山札のドロー → Trash の並べ替え → 相手の選択 → ドローの再開、相手が 1 点を得る）。
- **まだ証明していないこと**: 一般の置換効果の枠組み（M6）。セットアップ後の手札が 4 枚であることは、M2d で定理にした。

### M2b の実装の記録（2026-11-20）

- ファイル: `State/Decision.lean`（`Actor`・`ActionKind`・`Action`・`Frame`）、`Rules/{Add,Reorder,Setup,Frames}.lean`、`Spec/Legal.lean`、`Engine/Step.lean`、`Invariant/Step.lean`、`RiftboundDriver/Run.lean`。テストは `RiftboundTest/Setup.lean`。
- **セットアップは `step` で進む。** 初期状態（`GameState.initial`）は、Legend を Legend Zone に、Chosen Champion を Champion Zone に、残りの Main Deck と Rune Deck を各デッキに、Battlefield を `outOfGame` に置き、`pending` に最初のフレームを積む。シャッフル、Battlefield の選択、手番順は偶然の決定、マリガンはプレイヤーの決定で、`step` が受け取る。開幕の 4 枚のドローと、マリガン後のドロー・山札の下へのリサイクルは作業フレームを `advance` が進める。
- **ドローと Burn Out がつながった。** `draw p n` フレームは、空の山札に当たると `chanceBurnOut` フレーム（Trash の並べ替え）と `chooseBurnOut` フレーム（点を与える相手）を積んでから、ドローを続ける。山札も Trash も空なら繰り返し、fuel が尽きる。
- 証明した定理: `GameState.initial_wf`（初期状態は `WF`）、`step_wf`（**I3**）、`step_physIds`（**I1**: セットアップの全体で物理カードが保存される）、`step_mono`・`advance_mono`（**I15**: fuel の単調性）、`legal_of_step_ok`（`step` は `Legal` でない答えを受理しない。完全性）、`step_illegal`、`legalActions_iff`（**I6 の列挙の一致**）、`wf_reorder`・`physIds_reorder`、`addObject_wf`、`moveAll_*`。
- テスト: 8 つの seed で、セットアップが最後まで進み、各手札が 4 枚、山札が 35 枚、Battlefield が 2 枚場に出ることを検査する。同じ seed で同じ結果、物理カードの集合が開始から終了まで同じ、マリガンで 2 枚を脇に置いて 2 枚引き `chanceRecycle` が積まれること、違法な答えが拒否されること、fuel 不足が `fuelExhausted` になることも検査する。
- **M2b の PR で証明していなかったこと**（1 と 2 は M2c で済んだ。3 は残る）:
  1. **I4（内部エラーが起きない）と、`step` の健全性**（合法な答えが fuel 切れ以外で失敗しない）。`applyAction` が `none` を返さないことを、フレームの不変条件（フレームが指すカードが実際にそのゾーンにあること、など）を立てて示す必要がある。
  2. **セットアップ後の手札が 4 枚であることの定理**。テストで確かめただけ。`WF` に「Non-Board ゾーンのカードはそのゾーンの持ち主が Owner」（CR 056）を足す必要がある。
  3. **イベントの経路の置換の段**（design.md §6.6）。Burn Out は、フレームによる置換として動くが、一般の置換の枠組みは M6。
- 設計との違い: `Legal`・`legalActions`・`step` は `CardDB` を取らない（M4 で足す）。`RuleError.illegal` は理由を持たない。fuel は `step` の引数で、設定は `GameState.config` にある（design.md §6.1 のとおり）。

### M2a の実装の記録（2026-11-20）

- ファイル: `Core/Ids.lean`（`PlayerId`・`PhysId`・`ObjId`・`Timestamp`）、`State/{Zone,Object,GameConfig,Event,GameState}.lean`、`Rules/Move.lean`、`Rules/Actions/{Draw,Recycle,Channel,BurnOut}.lean`、`Basic/ListLemmas.lean`。テストは `RiftboundTest/Actions.lean`。
- 証明した定理: `allZones_nodup`、`Zone.key_inj`、`moveObj_wf`、`moveObj_fresh`（新しい ObjId は既存のどれとも異なる）、`moveObj_physIds`（I1 の 1 手）、`GameState.zone_unique`、`GameState.locate_eq`、ドローの `drawOne_wf`・`drawOne_physIds`・`drawOne_lengths`（山札 −1、手札 +1）、`recycleAll_wf`・`recycleAll_physIds`、`channel_wf`・`channel_physIds`、`burnOut_wf`・`burnOut_physIds`、`burnOut_points`（ちょうど 1 人の対戦相手が 1 点）。
- **イベントの経路（`perform`）は、M2a では型だけ。** `Event` を定義し、各プリミティブが発行する。置換・防止の段（design.md §6.6）は、Burn Out が決定（順序の偶然、対戦相手の選択）を必要とするので、フレームを作る M2b で足す。カードの置換効果は M6。
- **Burn Out** は、決定を引数で受ける純粋な関数にした（`order` と `opp`）。「ドローが空の山札に当たったら Burn Out に置き換える」手続きは M2b。
- **所有者の不変条件は M2b に回した。** `drawOne_lengths` は「山札のカードの所有者がそのプレイヤーである」を仮定に取る。M2b で `WF` に「Non-Board ゾーンのカードは、そのゾーンの持ち主が Owner」と「Owner と Controller が席に収まる」を足し、仮定を外す（CR 056）。
- `moveObj` は、Non-Board を出入りしたら、Controller を Owner に戻し、疲労とダメージをリセットする（CR 124.1）。


**実装**
- `PlayerId` / `PhysId` / `ObjId` / `CardId` / `Timestamp` を定義する。
- ゲームオブジェクト（種別: カード / トークン / Chain 上の能力）、ゾーン（エンジン内部用の `setAside` と `outOfGame` を含む）、`GameConfig`、`GameState`、`WF`（構造の条件だけ）を定義する。オブジェクトの表は `Std.ExtTreeMap` にする。
- 唯一のゾーン移動プリミティブ `moveObj` を作る。Non-Board ゾーンを出入りしたら、新しい ObjId を払い出す（124）。移動後の ObjId を返す。
- **イベントの経路 `perform` を作る**（提案 → 置換・防止 → 適用 → 発行。[design.md §6.6](design.md#66-イベントの経路)）。
  - 置換の段に入れるのは、ルール自身が持つ置換である Burn Out（432.5）だけ。カードの置換効果は M6 で足す。
- Draw（414）、Recycle（417）、Channel（431）、Burn Out（432）を、この経路の上に作る。
- **エンジンの骨格を作る**:
  - フレーム（`choose` のうちマリガン、`chance`）と、`Action`（行為者 + 内容）。
  - 1 歩の関数 `microStep`、それを fuel の回数だけ繰り返す `advance`、`step`。
  - `Legal` の最初の版（`Decidable` つき）と、`legalActions`。`step` は受理の判定に `Legal` を使う。
  - マリガンは、「脇に置くカードを 1 枚選ぶか、終える」決定の列にする（決定の粒度: [design.md §6.2](design.md#62-決定要求と継続)）。
- セットアップ（110-118）を `step` で進める:
  - Legend と Chosen Champion の配置
  - Battlefield の用意（113）。Duel では各自 3 枚から 1 枚をランダムに選ぶ（487.5）
  - シャッフル、手番順、4 枚引く、マリガン（脇に置く → 引く → Recycle）
- `RiftboundDriver` の最小版を作る: seed つき乱数で偶然の決定に答える。

**証明（L1〜L3）**
- I1、I2。`moveObj` と、Draw・Recycle・Channel の「適用」の段が `WF` を保存すること。
- セットアップの遷移について I3 と I4。
- I15（fuel の単調性）。`advance` の定義から、fuel についての帰納法で示す。
- マリガンと偶然の決定について I6（`Legal` との一致。偶然の決定の `Legal` は `List.Perm`）。
- Main Deck が空でなければ、draw で手札が 1 増え、Main Deck が 1 減る。空なら Burn Out を経由する（315.4.b）。
- Burn Out では、ちょうど 1 人の対戦相手が 1 点を得る（432.2.c）。
- Non-Board ゾーンを経由した後の ObjId は、どの既存 ObjId とも異なる（124）。
- セットアップ直後の各手札が 4 枚である。

## M3: ターン骨格と資源（CR 301-317, 160-168, 430, 445, 649-651, 734-738）

**M3 は 2 つに分けて進める。** 前半（ターンの骨格: フェイズ、手番の受け渡し、投了と勝敗）を先に作り、後半（資源: Rune Pool、Add 能力、Pay、I8、I5、追加ターン）をその上に作る。

### M3 I5（進行性）の実装の記録（2026-11-21）

- ファイル: `Invariant/Progress.lean`。
- **不変条件 `StackInv`**: ゲームが終わっていなければ、スタックの底のフレームは `priority`・`beginTurn`・`setupHands`・`chanceTurnOrder` のどれか（`BottomOk`）。この 4 つは、別の底のフレームに置き換わることはあっても、空になることがない。`applyFrame`・`microStep`・`advance`・`step` のすべての腕で保たれることを示した（`applyFrame_stack`・`microStep_stack`・`advance_stack`・`step_stack`）。補題 `BottomOk.replace`・`pop`・`swap` が、フレームを降ろす・差し替える腕を一括で片づける。
- **`TopIdle`**: `step` が返す状態の先頭は作業フレームでない（`advance_idle`・`step_idle`）。
- **定理 `Reachable.progress`（I5）**: 到達可能で、終わっておらず、プレイヤーが 2 人以上のゲームでは、`legalActions` に投了以外の答えがあるか、先頭のフレームが偶然の決定を求めている。マリガン（`mulliganDone`）、Burn Out の相手の選択（2 人以上なら相手がいる）、Main Phase（`pass`）は、必ず答えがある。
- **定理 `chance_answer_exists`**: 偶然の決定にも合法な答えがある。シャッフルする場所がゲームのゾーンであること、Battlefield を選ぶプレイヤーに Battlefield が 1 枚あること（`Frame.chanceReady`）を前提にした。この前提は、次の節で不変条件から導いた。
- **追加ターン（CR 734-738）は、まだ作っていない。** 追加ターンを与えるカード効果は M4 以降に入るので、そこで作る。

### M3 I5 を無条件にする（2026-11-21）

- **`GameState.initial` がデッキの合法性を求めるようにした。** `GameConfig.Valid`、デッキの数がプレイヤーの数であること、すべてのデッキが `DeckValid`（CR 101-103）であること。どれかが偽なら `none`。`GameConfig.Valid` には「デッキが Battlefield を 1 枚以上持つモード」（CR 487.5）を足した。
- ファイル: `Invariant/Setup.lean`。
- **`GameState.initial_setup`**: セットアップした状態は、プレイヤーが 2 人以上で、どのプレイヤーも Battlefield を 1 枚以上 `outOfGame` に持つ。デッキに足したカードは、どのゾーンからも減らない（`Grows`、`addDecks_grows`）ことと、合法なデッキの Battlefield の枚数がモードの値であること（`DeckValid.battlefields_length`）から出す。
- **不変条件 `SetupInv`**: プレイヤーが 2 人以上で、スタックがセットアップのフレームの後ろ半分のままか（このとき、まだ選ばれていない Battlefield は、選ぶカードがある）、セットアップのフレームが残っていない。セットアップのフレームは 1 つずつしかない（`startFrames_nodup`）ので、あるプレイヤーの選択が他のプレイヤーの Battlefield を減らすことはない。`applyFrame`・`microStep`・`advance`・`step` と投了で保たれる。
- **定理 `Reachable.progress`（I5）** は、プレイヤーが 2 人以上という前提が要らなくなった（前の版は `progress_of_players`）。**`Reachable.exists_legal`**: 終わっていない到達可能なゲームには、投了以外の合法な答えが必ずある（プレイヤーの答えか、偶然の答え）。
- **注意**: 求めているのは Core Rules の合法性（`DeckValid`）。大会フォーマットの合法なデッキは、`constructedDeckValid_deckValid`（I13）で Core Rules の合法性に落ちるので、そこを経由したデッキも通る。

### M3 後半（資源）の実装の記録（2026-11-20）

- ファイル: `State/Pool.lean`（`RunePool`・`Payment`）、`Rules/Resources.lean`（`applyRune`）、`Rules/Objects.lean`（`exhaustObj`）、`Invariant/Resources.lean`。テストは `RiftboundTest/Resources.lean`。`GameState` に `pools`、`Object` に `runeDomain` を追加。
- **Rune Pool**（CR 166）: Energy と、6 つのドメインごとの Power。自然数なので負にならない。Main Phase の開始時と Ending で空になる（CR 167）。
- **Basic Rune の 2 つの Add 能力**（CR 164.2）: Main Phase で、手番のプレイヤーが自分の Base の Rune に対して使える。Exhaust（Ready な Rune を Exhaust して Energy 1）と Recycle（Rune Deck の下に戻して、その Rune のドメインの Power 1）。**Add 能力は即座に解決する**（CR 430.2 の Chain 経由の振る舞いは M4）。
- **Pay**（CR 445）: `RunePool.spend`。Energy と、ドメインを選んだ Power の列を払う。足りなければ `none`。カードのコストをこの `Payment` に直す部分（`[A]` と `[C]` の解決）は、カードをプレイする M4 で作る。
- 証明した定理（**I8**）: `RunePool.total_spend`（**払うと、ちょうど払っただけ Pool から減る**）、`total_addEnergy`・`total_addPower`、`applyRune_adds_one`（**Add 能力が加えるのはちょうど 1**、他のプレイヤーの Pool は変わらない）、`applyRune_recycle_zones`・`channelOne_zones`（**Recycle と Channel で、Base と Rune Deck にある Rune の総数が保存される**）、`microStep_main_pools`・`microStep_ending_pools`（**Main Phase の開始時とターン終了時に Pool が空**）。`WF`・`OwnerOk`・I1・`HandInv`・`step_sound`・`legalActions_iff` は、Rune の能力を含めて引き続き証明済み。
- **設計の判断**: Rune のドメインは、オブジェクトを作るときに `CardDB` から**写し**として `Object.runeDomain` に持つ（`GameState.initial` が `CardDB` を取る）。エンジンの `step` と `Legal` は引き続き `CardDB` を取らない。導出（Layers）は M6。Rune の能力は、Owner が使うプレイヤーである Rune にだけ使える（Control の変更は M6）。
- **追加ターンは、さらに次の PR にした。** I5 は次の節のとおり済んだ。

### M3 前半の実装の記録（2026-11-20）

- ファイル: `State/Phase.lean`（`Phase`・`GameResult`）、`Rules/Objects.lean`（`mapObjects`）、`Rules/Frames.lean`（`beginTurn`・`phase`・`priority` のフレーム）、`Invariant/Turn.lean`。テストは `RiftboundTest/Turn.lean`。`GameState` に `phase`・`turn`・`active`・`result` を追加。
- **ターンの流れ**: 手番順が決まりマリガンが終わると `beginTurn` が走る。手番のプレイヤーは手番順を回して決まる（CR 118）。ターンは Awaken（手番のプレイヤーが Control する物を Ready: CR 315.1）→ Beginning（スタブ）→ Channel（2 枚。後手の最初のターンは 3 枚: CR 315.3, 487.7）→ Draw（1 枚。空なら Burn Out）→ Main の順で、手番のプレイヤーが `priority` を持つ。`pass` で Ending（全 Unit を Heal: CR 317.2）に進み、次のターンが始まる。
- **投了**（CR 649-651）: 決定要求と無関係に、どのプレイヤーにもいつでも合法。1v1 では相手が勝ち、スタックが空になる。終わったゲームは、どんな答えも違法。3 人以上は M9。
- 証明した定理: `turnFrames_eq`・`turnPhases_chain`（**I9 のフェイズの順序**）、`microStep_phase`（フェイズのフレームは、ゲームのフェイズをそのフェイズにする）、`step_concede`（投了の効果）、`step_over`（終わったゲームは何も受け付けない）、`turnPlayerAt_alternates`（**1v1 で手番が交互になる**）、`readyOf_idem`（**Ready の冪等性**: CR 416.1.b）、`mapObjects_ready_idem`、`channel_ownerOk`・`channel_sameMeta`。`WF`・`OwnerOk`・I1・`step_sound`・`legalActions_iff` は、新しいフレームと投了を含めて引き続き証明済み。
- **`HandInv` の変更**: 手札が 4 枚という条件は、セットアップの間（`phase = setup` かつ `result = none`）だけに限った（ターンが始まると手札は増える）。`Reachable.opening_hands` は「最初のターンの開始だけが残っている（`pending = [beginTurn]`）」ときの定理になった。
- **設計の変更**: `applyAction` を、投了と、フレームへの答え（`applyFrame`）に分けた。`Legal` は、フレームへの答え（`LegalFrame`）か投了（`LegalConcede`）で、ゲームが終わっていないこと。`MoveSpec` に「ゾーン・オブジェクト表・カウンタ以外は変わらない」（`SameMeta`）を足し、将来の状態の項目が増えても移動の補題が壊れないようにした。
- **まだ作っていないもの（M3 前半の時点）**: Rune Pool と Basic Rune の Add 能力、Pay（資源の会計 I8）、Main Phase の開始時と Ending に Rune Pool を空にすること（ここまでは M3 後半で済んだ）、I5（進行性）、追加ターン（CR 734-738）、Beginning Step の Scoring（M5）、Ending Step の「このターン」効果の失効。Pass と「ターン終了」は、Chain が無い Main Phase では同じなので `pass` 1 つにした。

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
- `GameResult`（勝者あり / 引き分け）と、終局の状態。引き分けを使うのは M5b から。
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

## M3b: 効果 IR の構文の先行検証（カードデータ、CR 408-446 の語彙）

解釈器と証明を作る前に、IR の形を実際のカードで確かめる。ゲーム進行には依存しないので、M1 の後ならいつ進めてもよい。M4 に入る前に終える。

**前提**: カードの公式文面はコミットし、1 弾 1 ファイルにする（[design.md §12](design.md#12-決定事項2026-11-20) Q1）。

**実装**
1. [card-data.md](card-data.md) のパイプラインを作る: 取得 → 正規化 → `RiftboundCards/<Set>.lean` の生成ブロックの更新。対象は Origins と Proving Grounds。
2. IR の構文を型として定義する: `Effect`、`Selector`、`Amount`、`Condition`、`Trigger`、`Cost`、`Duration`、`StaticMod`、選択の宣言と `EffectDef`、`Value` と `Env`（[design.md §7.2](design.md#72-構成要素初期案)）。解釈器はまだ書かない。
3. **構文だけの転記**: Origins と Proving Grounds のカードを、IR の値として書く。意味は与えない。実装状況は `drafted` にする。
   - 少なくとも、[card-data.md §7](card-data.md#7-モデルにとって難しいカード先に設計で考慮しておくもの) の難しいカードと、出現の多い上位 100 テンプレートを覆う。
4. 書けなかった文を一覧にする。足りない語彙（プリミティブ、Selector、Trigger、hook の種類）を洗い出し、design.md §7.2 と §7.3 を更新する。
5. カバレッジ表に、「IR で書けた割合」と「`custom` を使った数」を出す。

### M3b-6 2 回目の転記とカバレッジ表の実装の記録（2026-11-21）

- **作ったもの**: `scripts/transcribe.py`（決まった型の文だけを IR にする）、`scripts/coverage.py`（`docs/coverage.md`。`verify.sh` で `--check`）。
- **結果**: 78 枚を書いた。**合計 117 枚が `drafted`（1,103 枚の 10.6%）**。IR の不足は、このバッチでは新しく見つからなかった（型に合う文だけを書いたため）。
- **わかったこと**: カードの文の型は、長い裾野になっている。書けなかった 1,159 行は 1,105 種類で、最多でも 6 回。文の型を足す方式は、収穫が急に減る（[ir-gaps.md](ir-gaps.md) §5）。
- **見つけた誤りを直した**: 装備品 35 枚の `effect` 欄（付けた Unit に与える文）を、M3b-1 の正規化が捨てていた。`effectText` として持ち、生成ブロックに載せた。
- **M3b の完了条件**（書けなかった文の一覧がある。それを受けた IR の改訂が済んでいる）は、一覧は 2 回分あり、改訂は 1 回目で 20 件入れた。**上位 100 テンプレートを覆う**という目標は、型の分布が長い裾野だったので、そのままでは達成できない。M3b を閉じて M4 に進むかを、ユーザーが決める。

### M3b-5 静的な検査（`CardDB.WF`）の実装の記録（2026-11-21）

- **ファイル**: `Card/IR/Check.lean`。テストは `RiftboundTest/Check.lean`。
- **検査すること**（Boolean の関数で、`decide` と `#guard` で動く）: 変数が束縛されてから使われる（`Amount.var`・`Selector.var`）、`Selector.slot i` の番号が `EffectDef.choices` の対象枠の数より小さい、X は X を選ぶ宣言があるときだけ使う、`chooseOne` のモードの数が `Choice.mode` の宣言と一致する、`it` は `forEach`・`grant`・`delayed` と、誘発型の能力でだけ使う、置換前の量とプレイヤー（`eventAmount`・`eventPlayer`）は置換の中でだけ使う。
- **`CardDB.WF`** は、「識別子が一意」（`IdsUnique`）と「すべてのカードが `CardDef.StaticOk` を満たす」の組になった。
- **結果**: **転記した 39 枚は、すべて検査を通った。** 1,103 枚の `CardDB.WF` が `decide` で通る。転記が間違っているときに落ちることは、1 つの誤りだけを持つカードなどのテスト 22 件で確かめた。
- **証明した定理**: `Selector.ok_slot`（宣言した番号だけが有効）、`Amount.ok_var`、`Effect.ok_bind`、`EffectDef.slot_ok_iff`（有効な番号は、宣言した対象の数より小さいものすべて）、`Effect.ok_nop`、`CardDef.staticOk_of_no_effects`。
- **まだ検査しないもの**: `CustomId` の存在（ハンドラの表がまだ無い）、トークンや Tag の存在、解決時の型（`Selector` の指すものが Unit かどうか）。

### M3b-4 最初の転記の実装の記録（2026-11-21）

- **転記した範囲**: Proving Grounds の 24 枚と、設計で挙げた難しいカードなどの 22 枚。**46 枚のうち 39 枚が IR の値として書けた**（`drafted`）。書けなかったのは 7 枚（トークン、コピー、Spell の Control 奪取、多人数、トークンの置換）。一覧は [ir-gaps.md](ir-gaps.md)。
- **IR の改訂**: 転記で見つかった不足 20 件を IR に足して直した（`ir-gaps.md` §2）。主なもの: `Ability.passive` の条件、`Speed`、`Occurrence`、`Dest`、`Filter.at_` と `alone`、`Effect.replaceNext` と `preventNext`、プレイヤーに起きる誘発（`youConquer`・`youHold`）、誘発回数・得点・資源の hook（`triggersExtra`・`victoryScorePlus`・`entersReady` など）。補助関数は `Card/IR/Build.lean`。
- **近似したもの**: 6 件（Deathknell、Smite の「死ぬとき」、Forgotten Monument の期間など。`ir-gaps.md` §4）。**転記した文が意味どおりかは、解釈器とシナリオテストができるまで確かめられない。**
- **まだ無いもの**: 出現の多いテンプレートの上位 100 種の転記、カバレッジ表（`coverage.py`）。静的な検査は次の節で済んだ。

### M3b-3 IR の構文の型の実装の記録（2026-11-21）

- **ファイル**: `Card/IR/{Basic,Value,Expr,Prim,Effect,Ability}.lean`。`CardDef` に `abilities : List Ability` と `spellEffect : Option EffectDef` を足した（生成済みのカードは、どちらも空のまま）。テストは `RiftboundTest/IR.lean`。解釈器はまだ無い。
- **型**: `Side`・`Place`・`Quantity`・`Cmp`・`PlayerSel`・`Timing`・`Act`（小さな列挙型）、`VarId`・`CustomId`、`Value` と `Env`、`Amount`・`Filter`・`FilterList`・`Selector`・`Condition`（相互再帰）、`Prim`（34 のゲームアクション）、`Duration`、`Arg`・`ArgList`、`StaticMod`、`AbilityCost`、`TriggerEvent`・`Trigger`、`Effect`・`EffectList`（相互再帰）、`Choice`・`EffectDef`・`Limit`・`ReplaceEvent`・`Ability`。
- **等値性**: すべて `DecidableEq`・`Repr`・`Hashable` を derive できた。理由は、再帰する型が `List` や `Option` を自分自身の入れ子に持たず、専用のリスト型（`FilterList`・`EffectList`・`ArgList`）にしたから。**`Option` でも入れ子の帰納型になり、derive が失敗する**ことを確かめた。`BEq` を別に derive しない（`DecidableEq` から得る）。
- **設計の判断**: 条件分岐の else は `ifThen c t e` に `Effect.nop` を入れる。`Selector.slot i` が、`EffectDef.choices` で宣言した i 番目の対象を指す。`Amount` は自然数で、負の増減は `mightPlus` / `mightMinus` のように別の構成子にした。
- **まだ無いもの**: 変数の束縛・対象枠の番号の範囲の静的な検査（`CardDB.WF` の一部）、Replacement の `Effect` への組み込み、トークンの定義、Reflexive Trigger の細部。次の転記（M3b-4）で、書けなかった文から洗い出す。

### M3b-2 `gen_lean.py`（カードの Lean ファイルの生成）の実装の記録（2026-11-21）

- **作ったもの**: `scripts/gen_lean.py`（`--check` つき）。`RiftboundCards/<Set>.lean`（6 弾）と `RiftboundCards/Registry.lean` を生成する。`scripts/verify.sh` の 4 段目で `gen_lean.py --check` を実行する。テストは `RiftboundTest/Cards.lean`。
- **ファイルの形**: 弾ごとに、カード 1 種につき生成ブロック（公式文面の docstring と `def OGN_029.meta : CardDef`）と、その直後の手書きの部分（`def OGN_029 : CardDef := OGN_029.meta`、実装状況 `todo`）。生成スクリプトは生成ブロックだけを書き換え、手書きの部分とヘッダには触れない（手書きの編集を残し、改ざんした生成ブロックを戻すことを確かめた）。弾ごとの `cards`、全体の `allCards` と `db : CardDB` も生成する。
- **識別子**: カードの名前ではなく `cardId`（例: `OGN_029`）。エラッタや表記の揺れで名前が変わっても、手書きの効果との対応が切れない。読みやすさはドキュメントコメントの名前で補う。
- **ビルド**: 1,103 枚（約 2.5 万行）で `lake build RiftboundCards` は約 2 秒。`CardDB.WF`（識別子の一意性）は、テストの `#guard decide` で確かめる。
- **読み取れたもの**: 型、ドメイン、Energy と Power、Might、Might ボーナス、タグ、弾、先頭の行に並ぶキーワード（数値の引数、Equip・Repeat・Flow・Empower のコスト、Show Off の対象）。
- **読み取れなかったもの**:
  - supertype（Champion / Signature）は、公式ギャラリーに無いので空のまま。Chosen Champion の判定に使えない。
  - 2 つのドメインを持つカード（48 枚）と、ドメインの無いカードの Power のドメインは、分からないので任意のドメイン（`.any`）にして、コメントで印を付けた（全体で 56 枚）。
  - キーワードのコストを読めなかったもの（15 枚。Empower の「— Discard 1」など）は、引数なしにして印を付けた。
  - 型が空のトークン 2 種（Buff、XP Tracker）は `types := []`。
- **効果はまだ無い**: `CardDef` に `abilities` と `spellEffect` を足すのは IR を定義するとき（次の M3b-3）。

### M3b-1 取り込みのパイプライン（取得と正規化）の実装の記録（2026-11-21）

- **作ったもの**: `scripts/fetch.py`（公式ギャラリーから取得し、文面と数値だけを日付つきスナップショットにする）、`scripts/normalize.py`（論理カードに束ねる。`--check` で最新かを確かめる）。`scripts/verify.sh` の 4 段目で `normalize.py --check` を実行する。標準ライブラリだけで動く。
- **成果物（コミット済み）**: `data/snapshots/gallery-2026-11-21.json`（1,408 の印刷）、`data/cards/logical.json`（論理カード 1,103 種）。内訳は OGN 298、UNL 225、SFD 222、VEN 167、RAD 167、OGS 24。
- **わかったこと**:
  - 公式ギャラリーのページに入っている印刷は 1,408 件で、ギャラリー自身が報告する総数は 1,416 件。**8 件がページに無い**。ページネーションの API は、推測した URL では 404 だった。見つけるまでは 8 件を欠いたまま進める。
  - 型の補正は 37 件（欄が空 15 件、食い違い 22 件）。代替テキストの接頭辞で補った。トークン 2 種（UNL-T04 Buff、UNL-T08 XP Tracker）は型が空のまま。
  - supertype（Champion / Signature）は、公式ギャラリーに無いので、まだ埋めていない。Riftcodex で補うか、別の手がかりで推定するかは、`gen_lean.py` を作るときに決める。
  - 論理カードのうち 17 種は、印刷によって文面が違う（注釈文の違いは除く）。現時点の `cardId` は最初の印刷のもの。
- **次**: `gen_lean.py`（M3b-2、済）、IR の構文（M3b-3、済）、構文だけの転記（M3b-4）。

**証明（L0）**
- IR の型の等値性と `Repr`。入れ子の帰納型なので、等値性は相互再帰で書く（[lean-guidelines.md §5.4](lean-guidelines.md#54-deriving-と等値性)）。
- `CardDB.WF` の静的な検査（変数の束縛、対象枠の番号、参照の存在）を定義し、転記したカードが満たすことを検査する。

**完了条件**: 書けなかった文の一覧があり、それを受けた IR の改訂が済んでいる。

## M4: カードのプレイ・Chain・効果 IR v0（CR 325-340, 349-359, 399-407, 426, 430.2）

### M5c の実装の記録（2026-11-21）: 戦闘（Combat）

- **戦闘に入る**: 相手の Unit がいる Battlefield へも動ける（M5a の暫定の制限を外した）。Showdown が終わったとき、2 人の Unit がいれば Combat（`isCombat`）。Attacker は、その Battlefield を Contested にした人、もう一方が Defender（CR 466）。Ganking の Unit は、Battlefield から別の Battlefield へ動ける（CR 810）。
- **Combat Damage**（`combatDamage`・`assign`・`combatResolve` のフレーム）: 各陣営が Might を合計する（Attacker は Assault X、Defender は Shield X を加える）。Attacker から順に、相手の Unit に**致死ダメージを与える順番**を 1 体ずつ選ぶ（`assignPick`、Tank が先、全員を選び終えたら `assignDone`）。ダメージはその順に流れ、各 Unit が死ぬのに要る量を受け、残りは最後の Unit が受ける（`greedy`）。両陣営が終えたら、まとめて同時に与える（CR 467.2.c.1）。
- **Combat Cleanup と結果**（`combatResolve`）: 致死ダメージの Unit は Cleanup が kill し、全 Unit を Heal し、Defender の Unit が残っていれば Attacker の Unit を Recall（Base へ戻す）。その後は Showdown の終わりと同じで、Unit が 1 人だけに残っていれば、その人が Control を得て Conquer で Score する（防御側の Conquer も、CR 468.5.e のとおり起きる）。
- **証明**:
  - **最初の関係仕様（L5）**: `AssignOk`（CR 467.2.c を、エンジンの聞き方と独立に書いた規則: 全部のダメージを割り当てる、致死ダメージの前に次の Unit へ割り当てない、最後以外は致死量を超えない）と、`greedy_spec`（致死ダメージを順に与え、残りを最後の Unit に与える割り当ては、`AssignOk` を満たす）。
  - `assign_exists`: **割り当ての決定は行き止まりにならない**（どの途中状態でも、合法な答えがある。Tank を飛ばせない規則の下でも）。`mem_legalAssigns`（列挙は合法な答えだけ）。
  - 新しい行動・フレームについて、`WF`・I1・`OwnerOk`・`StackInv`・`HandInv`・`SetupInv`・`step_sound`・`legalActions_iff`・I5 が成り立つ。`combatResolve_safeP`・`dealAll_safe`・`recallObj_safe` を `Safe` から組んだ。
- **テスト**: `greedy` の例、Combat が Showdown の後に始まること、両方が致死で全滅して Control を失うこと、Tank が先で全員を選び終えて `assignDone` できること、`need`（致死に要る量）、Assault と Shield、Ganking、Combat Cleanup（Heal、Attacker の Recall、Defender が Control を保つ）。デモは seed 1 で、戦闘と Recall を含む 24 ターンの末に P1 が 8 対 1 で勝つ。
- **ビューア**: 割り当て（Unit を選ぶ・確定）がログに出て、Contested と支配が Battlefield の列に出る。
- **まだ無いもの**: Stun（CR 424）、Backline（CR 826。M8b で足すので、割り当ては順番の制約を足せる形にしてある）、Gear と他人の Base の Permanent の Recall（CR 323.6）、Combat の Staged（CR 323.8-323.9）と複数の Battlefield で同時に起きる Contested の順番、3 人以上、`Disarm`。I12（Cleanup と Combat の停止）と、I17 の全体の形。割り当ての「最後の Unit が残りを受ける」は、他に受け手がいないときの規則（CR 467.2.c.4）に対応するが、**割り当てた順を `greedy` で決める解釈**であり、公式の裁定と照合していない。

### M5a の実装の記録（2026-11-21）: Battlefield、Standard Move、Cleanup、Showdown、得点、勝利（戦闘を除く）

- **M5 を 2 つに分けた**: M5a は戦闘を除く部分（この記録）、**M5c が戦闘**（Attacker / Defender、ダメージの割り当て、Recall、戦闘のキーワード）。M5b（マッチと大会の手続き）は名前を変えない。
- **Battlefield の属性**（`Object`）: `loc`（Battlefield にいる Unit の、その Battlefield。Non-Board ゾーンへ出ると消える）、`control`（支配者。CR 190.6）、`contested`（Contested を付けたプレイヤー。CR 190.3）、`scored`（今ターンにこの Battlefield を Score したプレイヤー。CR 472）。Unit は Battlefield Zone に置かれ、どの Battlefield にいるかは `loc` で持つ。
- **Standard Move**（`standardMove unit dest`、`Rules/Battlefield.lean`）: 自分の Main Phase に、Ready の Unit が、Base から Battlefield へ、または Battlefield から Base へ動く。Exhaust する。支配していない Battlefield に来た Unit は、その Battlefield を Contested にする。`moveOk`（合法）、`applyMove`、`legalMoves`（列挙）、`mem_legalMoves`（列挙は合法な手だけ）、`applyMove_isSome`、`applyMove_safe`。**1 回に 1 体だけ**（複数を同時に動かす CR 144.3 は後）。
- **Cleanup**（`cleanup` フレーム。作業）: 状態が変わらなくなるまで 1 手ずつ繰り返す（CR 322）。手順は、勝者の宣言（323.1）、致死ダメージの Unit を Trash へ（323.4）、Unit のいない支配者から Control を外す（323.5）、Contested の整理（323.10）、Neutral Open なら Contested な Battlefield の Showdown を始める（323.11）。**ダメージで死ぬのは、解決の直後ではなく Cleanup になった**（M4c の前倒しをやめた。`dealObj` は damage を足すだけ）。Cleanup は、Spell の解決の後（`finishSpell`）、Beginning Phase と Main Phase の始まり、Standard Move の後に走る。
- **Showdown**（`showdown bf focus passes` フレーム。決定）: Focus は Contested を付けたプレイヤー。今は `pass` だけ（Action の Spell はまだ無い）。全員がパスすると、Unit が残っているプレイヤーが 1 人だけで、まだ支配していなければ、Control を得て Conquer で Score する（CR 348.2、`endShowdown`）。
- **得点**（`scoreBf`、`hold`）: Conquer は Showdown の終わり、Hold は Beginning Phase の Scoring Step（CR 315.2.b）。1 人が 1 つの Battlefield を 1 ターンに 1 回だけ（CR 472）。**Final Point**（CR 473.1.b）: Conquer で、点が Victory Score の 1 点手前以上なら、今ターンにすべての Battlefield を Score していないとき、点の代わりに 1 枚引く。勝者は、Victory Score 以上で、全員より点が多いプレイヤー（`GameState.winner`）。
- **証明**:
  - **I7**: `win_condition_unique`（2 人が互いより多い点を持つことはない）、`winner_spec`。
  - **I11**: `scoreBf_twice`（同じプレイヤーが同じ Battlefield を同じターンに 2 回 Score しても、何も変わらない。Conquer でも Hold でも）。
  - **I17（局所版）**: `Settled`（勝者がおらず、Cleanup の手順がどれも当てはまらない）、`Settled.no_lethal`（致死ダメージの Unit は盤面に無い）、`Settled.no_lostControl`、`cleanupFrame_pop_settled`（`cleanup` フレームが何もせず抜けるのは `Settled` のとき）。**「`priority` が先頭にある到達可能な状態は全部 `Settled`」という全体の形はまだ証明していない**（`runeAbility` や `playCard` が `Settled` を壊さないことの証明が要る）。
  - 新しい行動とフレームについて、`WF`・I1・`OwnerOk`・`StackInv`・`HandInv`・`SetupInv`・`step_sound`・`legalActions_iff`・I5 が成り立つ。`Safe` に点の変更を足した `SafeP`（`scoreBf_safeP`、`hold_safeP`、`endShowdown_safeP`）で、既存の証明は 1〜2 行の追加で済んだ。
- **テスト**: `RiftboundTest/Battlefield.lean`（Move の合法・違法、Contested、Showdown の開始と Focus、Conquer、2 体目は Contested にならない、相手の Unit は入れない、Base へ戻ると Control を失う、致死ダメージの Cleanup、Contested の整理、勝者、Hold、2 回目は 0、Final Point）。デモの 1 ゲームが最後まで進んで勝つこと（`RiftboundTest/Trace.lean`）。
- **ビューア**: Battlefield ごとの列に、Unit、支配者、Contested を表示する。Standard Move、Showdown でのパス、得点、勝者がログに出る。デモは、払えるカードがなければ Unit を Battlefield に送る。seed 1 は 19 ターン目に P0 が 8 対 7 で勝つ。
- **まだ無いもの（M5c 以降）**: 戦闘。**暫定の制限として、相手の Unit がいる Battlefield へは動けない**ので、Battlefield に 2 人の Unit が並ぶことはなく、Control を奪う手段もない。Ganking（Battlefield から Battlefield へ）、複数の Unit の同時の Move（144.3）、Recall（Gear や他人の Base の Permanent）、Showdown の中での Action と Reaction、Contested の Combat の Staged 化（323.8-323.9）、Hidden。I12（Cleanup の停止）と、I17 の全体の形。0 点のときに点を失う指示（194.4.a）は、点を失う手段が無いのでまだ。

### M4d の実装の記録（2026-11-21）: 効果の言語を広げる

- **解釈器に足したもの**（`Rules/Effects.lean`）: `ifThen`（条件で枝を選ぶ）、`forEach`（選んだ物ごとに本体を走らせる。`it` は `Env.it`）、`repeatN`、`banish`・`returnToHand`（`sendObj`: 持ち主のゾーンへ送る。`kill` も同じ）。`bind` と `draw` と `deal` の量は、盤面を読める `Amount.evalS`（`count`・`handSize` と四則・min・max）で計算する。
- **条件**（`Rules/Select.lean`）: `Condition.eval`。`always`・`not`・`and`・`or`・`cmp`・`exists`・`matches`・`yourTurn`。分からない条件は「答えられない」で、その指示は飛ばされる。
- **「解釈器が分かる」を数える**（`Rules/Understood.lean`）: `Effect.understood` などが、解釈器の各腕を静的に写す。`CardDef.spellRuns`（選択が全部「対象 1 つ」で、効果が全部分かる Spell）。**転記済み（drafted）の Spell 34 枚のうち 16 枚が、最初から最後まで動く**（`RiftboundTest/Cards.lean` の `#guard` が数を固定する）。
- **動かない 18 枚の理由**: 持続する Might の変更（`grant`: 9 枚。Layers = M6）、モード、複数の対象、選んだ Battlefield（`Filter.at_`、`here`）、遅延・置換（`delayed`・`replaceNext`・`preventNext`）、`takeControl`・`extraTurn`・`move`。
- **証明**: `runEffect_safe` は新しい腕を含めて成り立つ（状態を変えるのは `applyPrim` だけ）。`runEffect_mem`（解釈器が積むフレームは、Spell のフレームか `draw`）も新しい腕を含めて証明済み。**不変条件**は引き続き証明済み。
- **ビューア**: デモのデッキに、敵の Unit 全員に 1 ダメージを与える Spell（Sweep: `ifThen` と `forEach`）が入り、2 回で 2 体が Trash に行く。
- **まだ無いもの**: `may`・`doThen`・`chooseOne`（プレイヤーの決定が要る）、`grant`・`delayed`・`preventNext`・`replaceNext`（持続する効果）、`pick .one`、`discard`・`stun`・`buff`・`recycle`・`channel`・`score` などの残りのプリミティブ、`Filter.at_` と `here` などの場所。

### M4c の実装の記録（2026-11-21）: 対象を取る Spell と、`deal`・`kill`・`ready`・`exhaust`・`heal`

- **対象は行動に載せる**: `playCard card pay targets`。`pay` と同じく、プレイの一瞬の決定なので、新しい `choose` のフレームは足さなかった（フレームにすると、`StackInv`・`HandInv` などの不変条件がフレームごとに増える。行動に載せれば、`Legal` の 1 本の条件で足りる）。複数の選択（モード、X、追加コスト）や、選択が前の選択に依存するカードが来たら、フレームにする。
- **対象の宣言**（`Rules/Select.lean`）: `Choice.target .one side place fs` だけを扱う。`targetsOk`（選んだ組が合法か）、`targetTuples`（合法な組の全列挙）、`mem_targetTuples`（列挙は合法な組だけ）。候補は、`side`（Friendly・Enemy・Any）・`place`（Anywhere・Base・Battlefield）・`filters` に合う、盤面の物。分からない filter と place は「答えられない」（`none`）で、推測しない。分かる filter は、カードの種別・supertype・tag・名前・keyword・domain・印刷された Might と、Exhausted・Ready・ダメージあり・自分以外。
- **Chain 上の Spell が対象を持つ**: `Object.targets`。解決のとき、`Env.slots` に入り、`Selector.slot i` が読む。選ばれた物が盤面から消えていたら、その Selector は何も指さない（CR 340。効果は何もしない）。
- **プリミティブ**: `deal`・`heal`・`kill`・`ready`・`exhaust`。Selector は `self`・`slot`・`var`・`pick .all`。ダメージが Might に届いた物は、その場で Trash に行く（CR 417 の Cleanup を前倒ししたもの。Cleanup は戦闘（M5）で足す）。
- **状態を変える部品**（`Safe`）: 効果が盤面を変える操作は、`WF`・I1・`OwnerOk` を保ち、物・ゾーン・カウンタだけを変える。この `Safe s s'` を `modObj`（1 つの物の属性を変える。kind と owner を変えない）と `moveObj` から組み、`runEffect_safe` で解釈器全体が `Safe` だと示した。そのため、既存の不変条件の証明は、`run` の腕に `Safe` を 1 つ使うだけで済んだ。
- **証明**: `applyCast_targets`（Chain の Spell は、選んだ対象を持つ）、`castable_targets_inPlay`（Spell の対象は盤面の物）、`resolveFrames_slots`（解決は、持った対象を slot にして効果を走らせる）、`mem_legalPlays`（列挙は、カード・支払い・対象の合法な組だけ）、`runEffect_safe`。**不変条件**は引き続き証明済み。
- **ビューア**: デモのデッキに「敵の Unit に 2 ダメージ」の Spell（Spark）が入り、対象つきでプレイされ、Unit が Trash に行く。ログに「（対象: …）」が出る。
- **まだ無いもの**: 複数の対象・`upTo`・`exactly`・モード・X・追加コスト（選択のフレーム）、`here`・`inHand` などの place、条件（`ifThen`）、`forEach`、`pick .one`、Reaction と複数項目の Chain（I9）、Spell の速さ、Cleanup（ダメージによる死を Cleanup で行う）、Layers（現在の Might は印刷値のまま）。

### M4b の実装の記録（2026-11-21）: Spell と Chain の最小版、効果の解釈器 v0

- **Spell をプレイする**: `playCard` は Spell にも使える（対象や選択の無い Spell だけ。`castable`）。コストを払い、Spell は手札から Chain に載る（CR 354）。手番のプレイヤーから順に Priority が回り（`chainPass p n`）、全員がパスすると、Chain の一番上が解決する（`resolveChain`）。解決のあと、Spell は持ち主の Trash に行き（`finishSpell`）、手番のプレイヤーの `priority` に戻る。
- **効果の解釈器 v0**（`Rules/Effects.lean`）: `run` フレームが、残りの効果を 1 歩ずつ進める。意味を与えたのは、何もしない、列（`seq`）、変数の束縛（`bind`）、`draw`（`draw` フレームを積む）だけ。**実行できない指示は飛ばして、`Event.skipped` を出す**（エラーにしない。design.md §7.1）。`eval` できる量は、定数、変数、加減乗と min・max。
- **新しいフレーム**: `chainPass`（決定）、`resolveChain`・`run`・`finishSpell`（作業）。
- **証明**: `applyCast_pays_cost`（Pool がコストの合計だけ減る: I8）、`applyCast_zones`（手札が 1 枚減り、Chain が 1 枚増える）、`chainPass_last_resolves`（最後にパスした人が Chain を解決に回す）、`finishItem_trash`（解決した Spell は持ち主の Trash へ）。**不変条件**は、新しいフレームを含めて引き続き証明済み（`WF`・`OwnerOk`・I1・`StackInv`・`SetupInv`・`step_sound`・`legalActions_iff`・I5）。`HandInv` には「Spell のフレームはセットアップ中にスタックに無い」（`play`）を足した。
- **ビューア**: Chain の欄を足した。デモのデッキに、1 枚引く Spell が入り、プレイされると Chain に載り、全員のパスで解決する。
- **まだ無いもの**: 対象と選択の宣言（`choose` のフレーム）、Reaction と、Chain に複数の項目が載ること（I9: 後入れ先出し）、Spell の Action・Reaction の速さ、プレイ先の選択、プレイの巻き戻し（CR 358.5）、追加コストと割引、`deal`・`kill` など `draw` 以外のプリミティブと Selector、条件（`ifThen`）、能力の起動と誘発。転記済みの Spell で今プレイできるのは、`draw` だけで書けるもの。

### M4a の実装の記録（2026-11-21）: Unit と Gear をプレイする

- **`GameState.cards`**: カードの集合を、対局の固定の部分として状態に入れた（[design.md §6.1](design.md#61-中核-api)）。`GameState.initial` が入れる。エンジンの引数は増やしていない。
- **`playCard card pay` の答え**（`Rules/Play.lean`、`Rules/Pay.lean`）: Main Phase の `priority` で、手番のプレイヤーが、手札の Unit か Gear を、Rune Pool から払ってプレイする。カードは Base に出て、Unit は Exhausted で入る（CR 359）。Unit と Gear は finalize 直後に解決する（CR 337.2）ので、Chain には何も残らない。
- **コストと支払い**: `Cost.paidBy`（支払いがコストを払うか）、`Cost.payments`（払い方の全列挙）、`Cost.mem_payments`（列挙は、払う支払いだけ）。`[A]` の Power はどのドメインでもよく、`legalActions` は `[A]` の割り当てごとに別の手として並べる。
- **証明**: `applyPlay_pays_cost`（**Pool は、カードのコストの合計だけ減り、他のプレイヤーの Pool は変わらない**: I8）、`applyPlay_unit_exhausted`、`applyPlay_zones`（手札が 1 枚減り、Base が 1 枚増える）、`mem_legalPlays`（列挙は、プレイできる組だけ）。`WF`・`OwnerOk`・I1・`HandInv`・`StackInv`・`SetupInv`・`step_sound`・`legalActions_iff`・I5 は、新しい答えを含めて引き続き証明済み。
- **ビューア**: デモのプレイヤーは、払えるカードがあればプレイする。トレースに `playCard` の行が出る（手札から Base へ動く）。
- **まだ無いもの**: Spell と Chain（Priority の受け渡し、Reaction）、プレイ先の選択（Battlefield）、追加コストと割引、プレイの巻き戻し（CR 358.5）、能力の起動、効果の解釈器。`Accelerate` や `I enter ready` で Ready のまま入ることも、まだ無い。

**実装**
- プレイ手順の 6 段階（354-359）。
  - 選択（355）。何を選ぶかは、カードの選択の宣言から決める。
  - 総コストの決定（356）、支払い（357）。
  - 合法性の確認（358）。失敗したら、フレームに保存したスナップショットに巻き戻す。
- HOT FEPR（334-340）、Priority / Focus（311-313）。
- Add 能力を、Chain 経由で即座に finalize・解決する形にする（430.2）。
- タイミングの許可（Action 806、Reaction 813）。
- Unit・Gear は finalize 直後に即解決する（337.2）。
- Counter（426）、対象が不正になったときの処理（359.3.e。Ignored と Negated の区別を含む）。
- **hook の最小版**: `restrictions`、`permissions`、`costMods` は常に空を返す（[design.md §7.3](design.md#73-ルールの差し込み口hook)）。
- **効果 IR v0 の意味**: M3b で決めた構文のうち、draw、deal、kill、buff、ready、exhaust、stun、recall、banish と Selector v0 に意味を与える。
  - `microStep` に効果の解決を足す（列、繰り返し、決定要求による中断と再開）。
  - 解釈器は、どんな `Effect` に対しても全域にする。実行できない指示は飛ばし、診断用のイベントを発行する（[design.md §7.1](design.md#71-方針)）。
- 単純な呪文と、バニラの Unit・Gear を使えるようにする。

**証明（L2〜L4）**
- I9（Chain は後入れ先出し、Discretionary Action は Priority を持つプレイヤーだけ）。
- I16（Priority の受け渡し）、I18（任意の選択は必ず問われる）。
- プレイ・対象・コストのフレームについて I6。
- **L4 の開始**: IR v0 の各プリミティブと `microStep` が `WF` を保存する（I3 を効果の解決に広げる）。`microStep` の場合分けで示す。
- 合法性の確認に失敗したら、盤面がプレイ開始時のスナップショットと一致する（358.5 のモデル化）。

## M5: 移動・Showdown・戦闘・得点・Cleanup（CR 144, 190, 318-324, 341-348, 447-474）

**M5a（戦闘を除く部分）と M5c（戦闘）は実装済み**（下の「M5a」「M5c の実装の記録」）。以下は M5 全体の計画で、M5a で済んだ項目は M5a の記録を参照する。

**実装**
- Standard Move（144）、Contested（190.3）。
- Cleanup の 10 ステップ（323）。Showdown / Combat の Staged 化。
  - Cleanup の不動点の条件 `Settled` を定義する（[design.md §5.2](design.md#52-ゾーンとオブジェクト)）。
- Showdown（344-348）。
- Combat の 3 ステップ（466-468）。
  - ダメージの割り当て（467.2.c）。「次に割り当てる Unit と量を選ぶ」決定の列にする。
  - 戦闘結果と Recall。
- **戦闘に必要なキーワードの意味は、ここで一本化して実装する**: Tank（815）、Assault（807）、Shield（814）、Ganking（810）、Stun（424）。
  - Backline（826）は Unleashed で入るので M8b で足す。割り当ての実装は、それを足せる形にしておく。
- **スタブ**: 実効特性（`characteristics`）は「印刷値 + カウンター + 保存された期間つきの Might 修正」の暫定版にする。完全な Layers は M6 で差し替える。
  - 戦闘の関係仕様と補題は、`might : ObjId → Int` を引数に取る形で述べる。差し替えても証明が残る。
- Conquer と Hold（Scoring Step のスタブを実体化する）、Final Point（473.1.b）、勝利（323.1）。
- **バニラのデッキ同士で、1v1 が最初から最後まで遊べる状態にする。**

**証明（L2〜L5）**
- I7、I11、I12（できる範囲で）。
- I17（`priority` の時点で `Settled`）。
- **最初の関係仕様（L5）**: 戦闘ダメージの割り当て（467.2.c）を、実装と独立した `Prop` として書き、実装がそれを満たすことを示す。
- 得点が 0 のときに得点を失う指示は何も起こさない（194.4.a）。
- 移動・戦闘のフレームについて I6。

## M5b: マッチと大会の手続き（TR 403-410, 602, 604）

カードの能力に依存しないので、M5 の後ならいつ進めてもよい。

**実装**
- `Match`: ゲームの結果の列から、マッチの結果（勝ち数、引き分け、時間切れ時の判定）を決める（TR 404, 408.3）。
  - 骨格（`Match/Basic.lean`）は、Core Rules の 1v1 Match（Bo3: CR 488）と共有する。CR 488 の細目は、実装のときに原文で確かめる。
- 設定の妥当性 `GameConfig.Valid`: TR が手続きを定めていない、モードとフォーマットの組を除く。
- ジャッジによるループの引き分け（TR 505.6）: ジャッジを行為者とする `Action` を足す。大会の設定でだけ合法にする（[tournament-model.md §5](tournament-model.md#5-ループtr-505)）。
- ゲームの合間のサイドボード（Constructed は 1 対 1。最初のゲームと引き分けの後は不可）（TR 403）。
- 次のゲームの先手の決め方（前のゲームの敗者が選ぶ。引き分けなら同じ順）（TR 407）、引き分けの後の Battlefield の再利用（TR 406.1.b）。
- Bo1 の準備手順（任意の設定: TR 406.1.h）。
- 時間切れ: 時計の `Action`、現在のターンの後に追加 3 ターン、点差 2 点以上で勝ち（TR 408.2）。シングルエリミネーションの手順（TR 408.4）。
- 合意による引き分けと、ゲーム・マッチ単位の投了（TR 410）。
- フォーマットによるゲーム中の変更: Limited で Legend / Chosen Champion を使わない場合の追加ドロー（TR 602.4.a.5.b）。

**証明**
- I14（時間切れの後、ゲームは有限のターン数で終わる）。
- 引き分けたゲームはマッチの勝ち数に数えない（TR 404.3）。
- サイドボードの入れ替えの後も、デッキはフォーマットの要件を満たす（TR 403.4.c）。

## M6: 能力システムと Layers（CR 360-398, 475-482, 805-817）

### M7 の実装の記録（2026-11-23）: 追加のターン（1 枚）

- **エンジン**: `GameState.extraTurns`（追加のターンを取るプレイヤー）と `turnShift`（追加のターンの数。ターン順は、追加のターンが無かったように、続く）。`nextTurnPlayer` が、追加のターンを先に返し、`beginTurnStep` が、使った分を、減らして、ずらす。`Prim.extraTurn` を、動かす。`SameMeta` は、この 2 つの欄を、見ない。`first_turns` の定理に、追加のターンが無いという条件を足した。
- **動くようになったカード**: Time Warp（122。この後に、追加のターンを取る。これを追放する）。
- **動くカード**: 292 → **293 枚**。
- **近似として残したこと**: 追加のターンのあいだの、ターンの記録（ターンの数 `turn`）は、追加のターンも 1 つとして数える（時間切れの判定は、これを使う）。

### M7 の実装の記録（2026-11-23）: 山札の上を見たとき（1 枚）

- **エンジン**: `Prim.lookTop n`（山札の上 n 枚を見る。状態は変えない）と、`Event.lookedAt`。`TriggerEvent.seenOnTop`（山札にあるカードが、見られたときの誘発）。Vision、Stacked Deck、The Candlelit Sanctum、Baited Hook に、「見る」を足した。
- **動くようになったカード**: Nocturne, Horrifying（194。山札の上を見て（引かずに）、自分を見たとき、1 Power を払って、プレイしてもよい）。
- **動くカード**: 291 → **292 枚**。
- **レビューで直したこと**: Reinforce（上 5 枚を見る）にも、「見る」を足した。
- **近似として残したこと（レビュー）**: Stacked Deck で、手札に入れるカードは、先頭のものに決まる（選べない）。効果の解決のあいだに、山札を離れたカードの誘発は、働かない。
- **近似として残したこと**: 「見る」を出すのは、上の 4 つの仕組みだけ（Teemo, Strategist の「公開する」や、Promising Future は、含めない）。Vision は、「リサイクルするか」を尋ねる前に、見る。

### M7 の実装の記録（2026-11-23）: Energy で Hide する、Champion Zone から手札へ（1 枚）

- **エンジン**: Hide を持つカードに、「1 Energy を払って Hide する」能力を、足す（Swift Scout のような、パッシブ `hideWithEnergy` を持つ自分の物があるときだけ使える。`Condition.hidesWithEnergy`）。`Place.inChampionZone`（Champion Zone のカードを、選べる）。Hide の効果は、`hideEffect` に、まとめた。
- **動くようになったカード**: Swift Scout（263。Hide を、Power のかわりに、1 Energy で行える。1 Energy を払い、疲労して、自分の Teemo のユニットを、場か Champion Zone から、手札に入れる）。
- **動くカード**: 290 → **291 枚**。
- **レビューで直したこと**: Hide を無料にする効果（Guerilla Warfare）は、Energy で払った Hide には、Energy を戻す。
- **近似として残したこと（レビュー）**: 選んだ側（場か Champion Zone）に Teemo がいないと、コストだけが、使われる。
- **近似として残したこと**: 「場から」と「Champion Zone から」は、2 つの選択肢（「はい」で場、「いいえ」で Champion Zone）で書く。Hide の能力が、カードごとに 1 つ、増える。

### M7 の実装の記録（2026-11-23）: 呪文で選ばれたとき（1 枚）

- **エンジン**: `Event.chosenBySpell`（プレイヤーが、プレイした呪文で、対象を選んだ。呪文のプレイの、対象の数だけ出る）と、`TriggerEvent.chosenHere`（戦場の誘発: そのプレイヤーの、ここにいるユニットが、選ばれた）。`TurnEffect.chosenHere`（今のターンに、もう、働いた）。
- **動くようになったカード**: The Dreaming Tree（292。プレイヤーが、ここの、自分のユニットを、呪文で選ぶとき、そのターンの 1 回目なら、そのプレイヤーが 1 枚引く）。
- **動くカード**: 289 → **290 枚**。
- **近似として残したこと**: 「呪文で選ぶ」は、呪文のプレイのときの対象だけ（解決のときの選択は、含めない）。能力で選ぶ場合は、含めない。「選ぶ」は、プレイする時点で、対象が確定するとき。

### M7 の実装の記録（2026-11-23）: チェーンの上の呪文を、奪う（1 枚、エンジンの変更なし）

- **動くようになったカード**: Mystic Reversal（080。反応: チェーンの上の呪文のコントロールを得る）。呪文は、解決するとき、新しいコントローラーの効果として働き、持ち主の墓地に行く。
- **動くカード**: 288 → **289 枚**。
- **近似として残したこと**: 「新しく選び直してもよい」は、書かない（最初に選ばれた対象のまま）。

### M7 の実装の記録（2026-11-23）: 山札の上を見て、プレイして、残りをリサイクルする（1 枚、エンジンの変更なし）

- **動くようになったカード**: Baited Hook（242。1 エネルギーと Order を払い、疲労して、味方のユニットを殺す。山札の上 5 枚から、殺したユニットの Might ＋ 1 以下の、ユニットを、コストなしでプレイしてもよい。残りは、リサイクルする）。殺したユニットの Might を `bind` で覚え、プレイしたあと、山札が減った分から、リサイクルする枚数を数える。
- **動くカード**: 287 → **288 枚**。
- **近似として残したこと**: 「追放して、プレイする」を、山札から、直接プレイする。「見る」は、書かない。

### M7 の実装の記録（2026-11-23）: 死んだ後に、戻す、その 3（1 枚）

- **エンジン**: `TurnEffect.recallOnDeath`（ユニットに付ける印: 今のターンの、次の死で、戻す）と、`TurnEffect.recallDied`（死んだカードの印）。`killObj` が、印の付いたユニットが死ぬと、死んだカードに、`recallDied` を付ける（`noteDeath`）。
- **動くようになったカード**: Unlicensed Armory（023。手札を 1 枚捨て、疲労して、味方のユニットを選ぶ。このターン、次に、そのユニットが死ぬとき、Fury を払って、疲労させて戻してもよい）。
- **動くカード**: 286 → **287 枚**。
- **近似として残したこと**: The Boss と同じ（`docs/ir-gaps.md`）。

### M7 の実装の記録（2026-11-23）: 死んだ後に、戻す、その 2（1 枚、エンジンの変更なし）

- **動くようになったカード**: Zhonya's Hourglass（077。次に、味方のユニットが死ぬとき、かわりに、これを殺し、そのユニットを、疲労させて戻す）。The Boss と同じ書き方で、死んだ後に、墓地から戻す。ギアが、まだ場にあるときだけ（同時に 2 体が死んでも、1 体だけ）。
- **動くカード**: 285 → **286 枚**。
- **近似として残したこと**: The Boss と同じ（`docs/ir-gaps.md`）。

### M7 の実装の記録（2026-11-23）: 死んだ後に、戻す（1 枚、エンジンの変更なし）

- **動くようになったカード**: The Boss（269。自分のバフを持つユニットが死んだとき、1 Power を払い、これを疲労させて、そのユニットを、疲労させて基地に戻してもよい。征服したとき、これを準備完了にする）。
- **動くカード**: 284 → **285 枚**。
- **近似として残したこと**: 「死ぬかわりに」ではなく、「いったん死んでから、墓地から戻る」で書く。このため、死んだときの誘発（Deathknell など）と「ユニットが死んだ」記録が、働いてしまう。戻ったユニットは、新しいオブジェクト（バフは、死んだ時点で、すでに無い）。規則の「バフを使って」は、そのため、書かない。

### M7 の実装の記録（2026-11-23）: 殺して、Power を足す（1 枚、エンジンの変更なし）

- **動くようになったカード**: Malzahar, Fanatic（113。味方のユニットかギアを殺し、疲労して、アクション: 領域を問わない Power を 2 つ足す）。
- **動くカード**: 283 → **284 枚**。
- **近似として残したこと**: 「殺す」は、コストとして書く代わりに、効果の最初に書く。このため、能力は Chain に載り、相手が反応できる（規則では、Power を足す能力は、反応できない）。殺す対象は、場にある、ルーンと戦場を除く、味方の物（ユニットとギア。トークンは、ユニットかギア）。「ユニットかギア」を表す `or` が、フィルタに無いため。

### M7 の実装の記録（2026-11-23）: 呪文のときだけ使える、マナ能力（1 枚、エンジンの変更なし）

- **動くようになったカード**: Daughter of the Void（247。疲労して、反応として、領域を問わない Power を 1 つ足す。呪文をプレイするときだけ使える）。
- **動くカード**: 282 → **283 枚**。
- **近似として残したこと**: 「呪文をプレイするときだけ」は、「手札に呪文があるとき」で近似する（足した Power は、ユニットなど、呪文以外のプレイにも、使える）。

### M7 の実装の記録（2026-11-23）: Hide を、無料にする（1 枚）

- **エンジン**: `TurnEffect.hideFree`（このターン、Hide は、コストがかからない）と、`Condition.noted e`（このターンに、効果が記録されている）。`addPower` が、領域を問わない Power（`any`）も、足せる。Hide が、解決されるとき、`hideFree` なら、払った Power を、1 つ、戻す。
- **動くようになったカード**: Guerilla Warfare, Teemo（264。Hidden を持つカードを、墓地から、2 枚まで、手札に戻す。このターン、Hide はコストがかからない）。
- **動くカード**: 281 → **282 枚**。
- **レビューで直したこと**: Hide が、解決のときに、手札にあるカードのときだけ、Power を戻す。
- **近似として残したこと（レビュー）**: 戻すのは、領域を問わない Power（`any`）なので、別の領域のコストにも、使える。
- **近似として残したこと**: Power は、いったん払ってから、戻す（払えないときは、Hide できない）。「2 枚まで」は、2 回の「してもよい」で書く。

### M7 の実装の記録（2026-11-23）: 合計の上限つきで、いくつでも選ぶ（1 枚、エンジンの変更なし）

- **動くようになったカード**: Fox-Fire, Ahri（256。戦場のユニットを、合計 Might 4 以下になるまで、いくつでも殺す）。Might 1 から 4 のユニットを、Might の順に、「殺してもよいか」を尋ねる 8 段階（1 を 4 回、2 を 2 回、3 を 1 回、4 を 1 回）で書き、殺すたびに、Might の点数だけ、呪文に記録を付けて、残りを数える。
- **動くカード**: 280 → **281 枚**。
- **近似として残したこと（レビュー）**: Might の判定（`Filter.might`）は、パッシブ（オーラ）による増減を、含まない（バフ・装備・持続する変更は、含む）。
- **近似として残したこと**: Might 0 のユニットは、扱わない。選べるのは、段階ごとに、同じ Might のユニットの 1 つで、Might の小さい順に、尋ねる。

### M7 の実装の記録（2026-11-23）: 好きなだけ、払う（1 枚）

- **エンジン**: `Amount.notes e`（このオブジェクトに、今のターン、プレイヤーが付けた、記録 `e` の数）と、`TurnEffect.unitPaid`。「好きなだけ払う」は、1 単位ずつ、払ってもよいか尋ねる（最大 12 回）形で書き、払うたびに、呪文に記録を付ける。
- **動くようになったカード**: Bullet Time, Miss Fortune（268。好きなだけ Power を払って、その分のダメージを、戦場の敵のユニットすべてに与える）。
- **動くカード**: 279 → **280 枚**。
- **近似として残したこと（レビュー）**: 払う Power の領域は、プールの先頭から、自動で選ぶ（Hide と同じ）。同じターンに 2 回撃つテストは、道具の制限（呪文の直後に、もう 1 枚の呪文は、撃てない）で、まだ無い。上限の 12 に、ログは出ない。
- **近似として残したこと**: 払える上限は 12。「はい」と答えるたびに、1 単位を払うので、途中で「いいえ」と答えても、後の質問で、また払える。

### M7 の実装の記録（2026-11-23）: ダメージを、好きなように分ける（1 枚、エンジンの変更なし）

- **動くようになったカード**: Volibear, Furious（041。攻撃したとき、5 ダメージを、ここの敵のユニットに、好きなように分けて与える）。1 ダメージの効果を 5 回、それぞれ、敵のユニットを選んで、与える。
- **動くカード**: 278 → **279 枚**。
- **近似として残したこと（レビュー）**: 選ぶのは、能力が解決されるときで、チェーンに置くときではない。また、解決のときの選択には、Deflect の追加コストが、かからない（これは、解決のときに選ぶ、すべてのカードに、共通のエンジンの近似。実際の規則では、対象を選ぶので、かかる）。
- **近似として残したこと**: 敵のユニットが 1 つもいなければ、何も起きない。最初に選んだユニットが、途中で死んでも、後の 1 ダメージは、別のユニットを選ぶ（ダメージは、1 つずつ、与えるので、死は、クリーンアップの後）。

### M7 の実装の記録（2026-11-23）: 超過ダメージを、数える（1 枚）

- **エンジン**: 戦闘ダメージの割り当てが終わるとき、攻撃側が、敵のユニットに割り当てた、致死量を超えるダメージ（超過ダメージ）を、ターンの記録にする（`excessOf`・`noteExcess`・`TurnEffect.excessDamage`）。`Condition.excessAtLeast n`。
- **動くようになったカード**: Tryndamere, Barbarian（034。征服したとき、5 以上の超過ダメージを、敵のユニットに割り当てていたなら、1 点を得る）。
- **動くカード**: 277 → **278 枚**。
- **近似として残したこと（レビュー）**: 実際の戦闘を最後まで通すテストは、まだ無い（`excessOf` と記録を、直接試している）。3 人以上の対戦は、まだ無い。
- **近似として残したこと**: 記録は、そのターンの、最後の戦闘のもの。戦闘ではなく、移動で征服したときも、そのターンの前の戦闘の記録が残っていれば、条件を満たす（「攻撃の後で」を、厳密には、見ない）。致死量を超える分は、割り当ての最後のユニットだけに、生じる。

### M7 の実装の記録（2026-11-23）: 戦闘ダメージを、最後に割り当てられる（1 枚）

- **エンジン**: `StaticMod.assignedLast` と `GameState.isLast`。ダメージの割り当ての順番で、これを持つユニット（Tank を持たないもの）は、ほかのすべてのユニットの後になる（`pickOk`）。「割り当てに、行き詰まりが無い」ことの証明を、広げた（`assign_exists`）。
- **動くようになったカード**: Caitlyn, Patrolling（068。戦闘ダメージを最後に割り当てられる。疲労して、自分の Might と同じダメージを、戦場のユニットに与える。戦場にいるときだけ）。
- **動くカード**: 276 → **277 枚**。
- **レビューで分かったこと**: キーワード Backline（最後に割り当てられる）は、まだ無い。`isLast` に足せば、同じ仕組みで動く。
- **近似として残したこと**: Tank と「最後」の両方を持つユニットは、Tank を優先する。「最後」のユニットが、複数いるときは、その間の順番は自由。

### M7 の実装の記録（2026-11-23）: いくつでも、バフを持てる（1 枚）

- **エンジン**: `StaticMod.anyBuffs` と `Object.extraBuffs`（最初のバフに足す、バフの数）。バフを与えると、増える（出来事も出る）。バフを使うと、先に減る。Might は、バフの数 × （1 ＋ そのターンの追加）。
- **動くようになったカード**: Lee Sin, Ascetic（078。疲労して、自分にバフを与える。バフはいくつでも持てる）。
- **動くカード**: 275 → **276 枚**。
- **近似として残したこと**: 「バフを持つ」の判定（`buffed`）は、1 つ以上持つ、で変わらない。
- **近似として残したこと（レビュー）**: 「バフをいくつでも使う」（Kraken Hunter・Albus Ferros）は、ユニット 1 つにつき、バフを 1 つだけ使う（Lee Sin の、複数のバフを、使い切れない）。

### M7 の実装の記録（2026-11-23）: 今のターンに、選んでいないものを、選ぶ（1 枚）

- **エンジン**: `TurnEffect.modeUsed n`（このターンに、モード `n` を選んだ）。`markOn` と `Condition.marked` で、使う。
- **動くようになったカード**: Udyr, Wildman（157。バフを使って、まだ選んでいない、4 つのうち 1 つ（戦場のユニットに 2 ダメージ、スタン、準備完了、このターン Ganking）を選ぶ）。
- **動くカード**: 274 → **275 枚**。
- **近似として残したこと**: すでに選んだモードも、選べるが、何も起きない（バフは、使われる）。規則では、選べない。
- **近似として残したこと（レビュー）**: 対象が無いモードも選べ、バフと、そのモードが、使われる。バフは、解決のときに使うので、応答で先にバフを失うと、効果が出ない。テストの道具に、「選択肢の何番目か」を答える仕組み（`Says.fromEnd`）を足して、4 つのモードを試した。

### M7 の実装の記録（2026-11-23）: 開いている戦場へ、ユニットを出す（1 枚）

- **エンジン**: `StaticMod.playToOpenBf`（味方のユニットを、開いている戦場へ出せる）と、`Filter.permitsOpenPlay`。ユニットのカードに、「その能力が場にあるとき、印刷されたコストを払って、開いている戦場へ出す」起動型の能力を、最後に足す（`CardDef.openPlay`）。Mageseeker Warden の制限は、この能力にも、効く。
- **動くようになったカード**: Miss Fortune, Buccaneer（193。自分を、開いている戦場へ出してもよい。場にいる間、味方のユニットも、開いている戦場へ出せる）。
- **動くカード**: 273 → **274 枚**。
- **レビューで直したこと**: 「相手はカードをプレイできない」が、戦場へ出す能力にも効く。Warden の制限と、手札の Miss Fortune の負例を、テストする。
- **近似として残したこと**: 印刷されたコストを払う（コストの軽減や、Accelerate は、使えない）。手札からだけで、Champion Zone や Hidden からは、開いている戦場へ出せない。`permitsOpenPlay` は、パッシブの条件を見ない。

### M7 の実装の記録（2026-11-23）: Hidden から出たカードを、覚える（1 枚）

- **エンジン**: `Object.fromHidden`（伏せたカードから、場に出た）。`Condition.fromHidden`（これが、伏せたカードから、出た）。
- **動くようになったカード**: Teemo, Strategist（121。防御したとき、または、伏せたカードから出たとき、メインデッキの上 5 枚の、Hidden を持つカードの数だけ、ここの敵のユニットに、ダメージを与え、5 枚をリサイクルする）。
- **動くカード**: 272 → **273 枚**。
- **レビューで直したこと**: デッキが 5 枚に満たないときは、あるだけをリサイクルする。伏せたカードから出た、本当の経路（Hide して、次のターンに出す）と、デッキの枚数が少ない場合と、相手の Teemo が防御する場合を、テストする。
- **近似として残したこと（レビュー）**: すでに基地にいるカードを、もう一度プレイしても、`fromHidden` を、消さない（`playFree` が、ゾーンの移動を、しないため）。
- **近似として残したこと**: 敵のユニットは、選択が必要（いなければ、リサイクルも起きない）。伏せたカードから出たユニットは、基地に出る（ここには、敵のユニットがいない）ので、実際には、防御のときだけ、ダメージが出る。

### M7 の実装の記録（2026-11-23）: 場所を入れ替える（1 枚）

- **エンジン**: `Prim.swapPlaces`（2 つのユニットが、場所を入れ替える。同じ場所なら何もしない。基地へ動かすことを禁じる戦場からは、動かさない）。
- **動くようになったカード**: Tideturner（199。プレイしたとき、味方のユニットを選んでもよい。これと、そのユニットが、場所を入れ替える）。
- **動くカード**: 271 → **272 枚**。
- **近似として残したこと**: 「選んでもよい」は、ユニットの選択は強制で、動かすかどうかだけが、任意（Stealthy Pursuer と同じ）。入れ替えで動くことは、移動として数えず、「動いたとき」の誘発も、起こさない（`sendToBf`・`sendHome` が、効果による移動のとき、そうであるのと同じ）。

### M7 の実装の記録（2026-11-23）: 呪文でユニットを殺したとき（1 枚）

- **エンジン**: `Event.killedBySpell`（呪文の `kill` の効果で、ユニットが死んだ）と、`TriggerEvent.killBySpell`（自分の墓地にあるカードの誘発）。
- **動くようになったカード**: Immortal Phoenix（037。呪文でユニットを殺したとき、1 エネルギーと Fury を払って、墓地から、これをプレイしてもよい）。
- **動くカード**: 270 → **271 枚**。
- **近似として残したこと**: 「呪文で殺す」は、呪文の `kill` の効果だけ（ダメージで死ぬのは、`killOnHit` を含めて、含めない）。1 つの呪文に `kill` が 2 つあると、誘発が 2 つ積まれ、2 つ目は（もう場に出ているのに）支払いだけが起きうる（墓地にあるかの確認が、まだ書けない）。

### M7 の実装の記録（2026-11-23）: 墓地にあるカードの、誘発（1 枚）

- **エンジン**: `TriggerEvent.conquerFromTrash`（自分が征服したとき、自分の墓地にある、このカードの誘発）。`detectOne` の `scored` が、征服のときに、墓地のカードを調べる。
- **動くようになったカード**: Super Mega Death Rocket!（252。ユニットに 5 ダメージ。征服したとき、手札を 1 枚捨てて、これを墓地から手札に戻してもよい）。
- **動くカード**: 269 → **270 枚**。
- **近似として残したこと**: 捨てるカードが、手札に無いときは、使えない（手札が 1 枚以上あることを、先に見る）。
- **近似として残したこと（レビュー）**: 誘発が Chain にある間に、このカードが墓地から出ると、捨てる処理は走る（戻す処理は、空振りする）。

### M7 の実装の記録（2026-11-23）: 相手が、自分のユニットを選んで、殺される（1 枚、エンジンの変更なし）

- **動くようになったカード**: King's Edict（237。それぞれの相手が、自分のユニットを 1 つ選び、それを殺す）。`eachPlayer .eachOpponent` の中で、「味方のユニット」を選ぶ。
- **動くカード**: 268 → **269 枚**。
- **近似として残したこと**: 1 対 1 の対戦を想定する（「まだ選ばれていない」ユニットの制限は、相手が 1 人なので、意味を持たない。3 人以上の対戦は、まだ無い）。

### M7 の実装の記録（2026-11-23）: 戦場ごとに、伏せられるカードを、1 枚にする（1 枚）

- **エンジン**: Hide の対象の戦場に、`Filter.hideRoom`（その戦場に伏せたカードが、1 枚未満。`StaticMod.extraHide` を持つ戦場は、2 枚未満）を足した。これまでは、戦場ごとの制限が、無かった（CR 811）。
- **動くようになったカード**: Bandle Tree（278。ここに、もう 1 枚、伏せてもよい）。
- **動くカード**: 267 → **268 枚**。
- **近似として残したこと（レビュー）**: 戦場の支配を失ったときに、相手の伏せたカードを、墓地へ送る規則（323.6.a）が無いので、古いカードも、数える。
- **近似として残したこと**: `extraHide` は、パッシブの条件を見ない（条件が `always` のカードだけを、想定する）。

### M7 の実装の記録（2026-11-23）: リサイクルしたときの出来事（1 枚）

- **エンジン**: `Event.recycled`（リサイクルしたプレイヤー）。`TriggerEvent.recycle`（自分がコントロールする場の物体の誘発）。`Prim.recycle` と `Prim.recycleTop` が、出す。
- **動くようになったカード**: Karma（235。リサイクルしたとき、味方のユニットに、バフを与える）。
- **動くカード**: 266 → **267 枚**。
- **レビューで直したこと**: ルーンのリサイクルでは、出さない。デッキの中のカードを、リサイクルする（並べ替える）ときも、出す。
- **近似として残したこと**: 出来事を出すのは、`recycle` と `recycleTop` の効果だけ（デッキの上から見て、残りをリサイクルする効果は、出さない）。`recycle` の効果ごとに 1 回（Stacked Deck のように、複数を並べると、複数回になる。「1 枚以上」は、本来、1 回）。

### M7 の実装の記録（2026-11-23）: 相手の制限を、パッシブで書く（1 枚）

- **エンジン**: `StaticMod.oppsPlayToBaseOnly`（相手は、ユニットを、基地にしか出せない: 戦場へ出す、手札の能力を、使えなくする）、`StaticMod.noReadyOfOpps`（呪文と能力は、相手のユニットとギアを、準備完了にできない: `readyEffect`）、`Filter.onBattlefield`（戦場にいる）。
- **動くようになったカード**: Mageseeker Warden（070）。
- **動くカード**: 265 → **266 枚**。
- **レビューで直したこと**: 誘発や効果としての `playTo`（Ava Achiever）は、止めるのではなく、基地へ出す（`playToOrBase`）。`Filter.onBattlefield` は、戦場のゾーンにいることも見る。
- **近似として残したこと**: 「戦場へ出す」は、効果が `playTo` だけの、手札の能力（Sneaky Deckhand など）だけを止める。準備完了の禁止は、`ready` の効果だけに効く（ユニットが、準備完了で場に出ることや、ターンの始めの準備は、止めない）。

### M7 の実装の記録（2026-11-23）: 引き分けで、全員を呼び戻す（1 枚）

- **エンジン**: `StaticMod.recallAllOnTie`。戦闘の終わりに、両方の陣営にユニットが残る（引き分け）とき、攻撃側のコントローラーがこの能力を持つなら、攻撃側だけでなく、すべてのユニットを呼び戻す（`combatResolve`）。
- **動くようになったカード**: Symbol of the Solari（227）。
- **動くカード**: 264 → **265 枚**。
- **近似として残したこと**: 引き分けは、「ダメージの後に、両方の陣営にユニットが残る」こと（攻撃側のユニットを呼び戻す、通常の場合）とする。

### M7 の実装の記録（2026-11-23）: Champion Zone から、ユニットをプレイする

- **理由**: `legalPlays` は手札だけを見るので、Champion Zone の Chosen Champion は、プレイできなかった（Hallowed Tomb のレビューで分かった）。
- **エンジン**: コスト `AbilityCost.fromChampionZone`。ユニットのカードに、「Champion Zone にあるとき、印刷されたコストを払って、これをプレイする」起動型の能力を、最後に足す（`CardDef.championPlay`）。能力が使える場所に、Champion Zone を足した（`abilityZones`・`abilityZoneOk`）。
- **レビューで直したこと**: 「相手はカードをプレイできない」が、この経路にも効く。
- **近似として残したこと（レビュー）**: 支払ったエネルギーと追加コストは、記録しない（`energyPaid`・`paid` は 0 と偽）。Accelerate は、選べない。能力としてチェーンに載るので、相手が反応できる。
- **近似として残したこと**: コストは、印刷されたもの（手札からのプレイが受ける、コストの軽減は、適用しない）。効果としてのプレイなので、プレイしたことの記録（Legion など）は、`playFree` の分だけ。

### M7 の実装の記録（2026-11-23）: Chosen Champion を、墓地から戻す（1 枚）

- **エンジン**: `Prim.returnChampion`（Champion Zone が空なら、自分の Chosen Champion を、墓地から Champion Zone へ戻す）。
- **動くようになったカード**: Hallowed Tomb（281。ここを保持したとき、Chosen Champion を墓地から Champion Zone へ戻してもよい）。
- **動くカード**: 263 → **264 枚**。
- **近似として残したこと**: カードのデータに、Champion と Signature の区別が無いので、Chosen Champion は「自分の伝説と同じタグを持つ、墓地の最初のユニット」とする（本物の Chosen Champion と、デッキの同名のコピーは、区別しない）。
- **レビューで分かったこと**: Origins の 12 枚の伝説は、どれも、同じタグを持つユニットが 2 枚ある（例: Kai'Sa は 039 と 112）。墓地の先頭の方が、戻る。また、Champion Zone のカードを、プレイする経路が、エンジンに無い（`legalPlays` は手札だけ）。

### M7 の実装の記録（2026-11-23）: 征服の効果を、効果で起動する（1 枚）

- **エンジン**: `Prim.activateConquer`（選んだユニットの、征服したときの誘発を、起動する。`Event.conquerActivated`）。
- **動くようになったカード**: Reckoner's Arena（286。ここを保持したとき、ここの自分のユニットの、征服の効果を、起動する）。
- **動くカード**: 262 → **263 枚**。
- **レビューで直したこと**: 文面は「ここのユニット」なので、敵のユニットも対象にする（効果は、そのコントローラーのもの）。
- **近似として残したこと**: 起動するのは、ユニット自身の `conquer` の誘発（Hunt を含む）。「あなたが征服したとき」の、伝説や戦場の誘発は、起動しない。

### M7 の実装の記録（2026-11-23）: Hidden から出したときの出来事（1 枚）

- **エンジン**: Hidden から出す（ユニット・ギア・呪文）と、`Event.hiddenPlayed` が出る（`hiddenPlay` の最初に、`TurnEffect.hiddenPlayed` を使う）。`TriggerEvent.playHidden`（自分がコントロールする場の物体の誘発）。
- **動くようになったカード**: Ember Monk（167。Hidden からカードをプレイしたとき、このターン +2 Might）。
- **動くカード**: 261 → **262 枚**。
- **近似として残したこと**: 「プレイしたカード」を、誘発の対象にはしない（Ember Monk は、自分のことだけを書く）。
- **近似として残したこと（レビュー）**: 出来事は、Hidden の能力が解決されるときに出る（起動したときではない）。

### M7 の実装の記録（2026-11-23）: バフを与えたときの出来事（1 枚）

- **エンジン**: バフを持たないユニットに、バフを与えると、`Event.buffed` が出る。`TriggerEvent.buff`。
- **動くようになったカード**: Mistfall（152。味方のユニットに、バフを与えたとき、Body を払い、これを疲労させて、そのユニットを準備完了にしてもよい）。
- **動くカード**: 260 → **261 枚**。
- **レビューで直したこと**: ドライバの Trace JSON に、`buffed` の出来事を足した（網羅的な `match` が、ビルドを壊していた）。

### M7 の実装の記録（2026-11-23）: ほかのユニットも Vision を持つ（1 枚、エンジンの変更なし）

- **動くようになったカード**: Gemcraft Seer（100。自分のほかのユニットを、プレイしたとき、デッキの一番上を、リサイクルしてもよい。Vision を、すでに持つユニットは、2 回にならない）。
- **動くカード**: 259 → **260 枚**。
- **近似として残したこと**: ほかのユニットが Vision を「持つ」ことは、プレイされたときの誘発として書いてある（キーワードを、実際には、与えていない）。
- **近似として残したこと（レビュー）**: Gemcraft Seer が 2 枚あると、Vision は 1 回分のはずが、2 回誘発する（誘発は、場にある源ごとに作られる）。

### M7 の実装の記録（2026-11-23）: 死んだときの様子を、ゲームに残す（2 枚）

- **エンジン**: 殺されたユニットが、バフを持っていたか、スタンしていたかは、死んだカード（墓地の物体）についての、ターンの記録になる（`TurnEffect.buffedUnitDied`・`stunnedUnitDied`。`noteDeath`）。`Condition.diedWith`（見ている物体が、その記録を持つ）。
- **動くようになったカード**: Vanguard Helm（228。バフを持つ味方のユニットが死んだとき、別の味方のユニットに、バフを与える）、Solari Shrine（072。スタンした敵のユニットが死んだとき、疲労させて、1 枚引いてもよい）。
- **動くカード**: 257 → **259 枚**。
- **レビューで直したこと**: ターンが変わると、ターンの記録（`turnFx`）を、すべて捨てる（古い記録で、毎回の走査が、遅くならないように）。バフだけで死んだユニットは Shrine を、スタンだけで死んだユニットは Helm を、動かさないことも、テストする。
- **近似として残したこと**: Solari Shrine の「あなたが殺したとき」は、「敵のスタンしたユニットが死んだとき」で判断する（殺した者は、見ない）。

### M7 の実装の記録（2026-11-23）: 一緒に動く（1 枚）

- **エンジン**: `Selector.locationOf`（物体がいる Battlefield。基地にいるものは、なし）。`Filter.movedFromHere` は、この物体が Battlefield なら、その Battlefield から、ユニットなら、そのユニットのいる場所（Battlefield か、基地）から、動いたかを調べる。
- **動くようになったカード**: Stealthy Pursuer（177。味方のユニットが、自分のいる場所から動いたとき、一緒に動いてもよい。行き先は、そのユニットの今いる場所）。
- **動くカード**: 256 → **257 枚**。
- **レビューで直したこと**: 動いたユニットが、解決の前に死ぬと、何もしない。
- **近似として残したこと**: 追従先は、解決するときの、そのユニットの場所（解決の前に、さらに動いていれば、その場所）。基地への、効果による移動は、移動として数えない。

### M7 の実装の記録（2026-11-23）: どこから動いたか（1 枚）

- **エンジン**: ユニットは、最後の移動の前にいた場所を、覚える（`Object.prevLoc`。標準の移動と、効果による Battlefield への移動）。`Filter.movedFromHere`（このターンの最後の移動が、この物体のいる場所からだった）。
- **動くようになったカード**: Back-Alley Bar（277。ここから動いたユニットは、そのターン、+1 Might）。
- **動くカード**: 255 → **256 枚**。
- **近似として残したこと**: 効果による、基地への移動（`moveHome`）は、動いた場所を、覚えない。

### M7 の実装の記録（2026-11-23）: ターンの終わりに、準備完了にする（1 枚）

- **エンジン**: 物体に付けるターンの記録 `TurnEffect.conqueredHere` と、条件 `Condition.marked`（その物体に、このターン、記録がある）。
- **動くようになったカード**: Targon's Peak（289。征服したとき、記録を付ける。ターンの終わりに、記録があれば、疲労した Rune を 2 つ準備完了にする）。
- **動くカード**: 254 → **255 枚**。
- **近似として残したこと**: ターンの終わりの誘発は、ターンプレイヤーのものだけが動くので、相手が、自分のターンに、征服したときの準備完了は、起きない。

### M7 の実装の記録（2026-11-23）: 動きと Hidden を止める、パッシブ（3 枚）

- **エンジン**: `StaticMod.noMoveToBase`（ここにいるユニットは、標準の移動で、基地へ戻れない。`moveOk` が見る）、`StaticMod.noHiddenReveal`（ここの、相手の Hidden のカードは、使えない。`guardOk` が見る）。
- **動くようになったカード**: Vilemaw's Lair（295）、Noxus Saboteur（018）、Treasure Trove（186。死んだとき、1 枚引いて、疲労した Rune を 1 つ引く。Chaos と疲労で、自分を殺す）。
- **動くカード**: 251 → **254 枚**。
- **レビューで直したこと**: Vilemaw's Lair は、効果による、基地への移動（`moveHome`）も、止める（Recall は、止めない）。Saboteur は、実際に Hidden にして、使えるかで、確かめる。
- **近似として残したこと**: Treasure Trove の「場を離れたとき」は、「死んだとき」だけを見る（手札へ戻る、追放される、は、見ない。たとえば、Pack of Wonders で、手札へ戻したときは、誘発しない）。

### M7 の実装の記録（2026-11-23）: Deathknell を、もう 1 回（1 枚）

- **エンジン**: 自分が支配する物体のパッシブ（`StaticMod.triggersExtra .die`）があるあいだ、自分のユニットが死んだときの Deathknell（キーワードを持つカードの、死んだときの誘発）は、もう 1 回、誘発する。
- **動くようになったカード**: Karthus, Eternal（236）。
- **動くカード**: 250 → **251 枚**。
- **近似として残したこと**: 「死んだとき」の誘発のうち、Deathknell のキーワードを持つカードのものを、すべて、Deathknell として数える。
- **近似として残したこと（同時の死）**: Karthus が、Deathknell のユニットと同時に死ぬと（戦闘など）、Karthus は、すでにいないので、追加の誘発は、起きない。

### M7 の実装の記録（2026-11-23）: Rune Deck の一番上を、めくる（1 枚）

- **エンジン**: `Filter.top n` は、Main Deck だけでなく、Rune Deck の上の n 枚も指す。
- **動くようになったカード**: Twisted Fate, Gambler（200。攻撃するとき、Rune Deck の一番上をめくって、リサイクルし、領域で分ける: Fury は、敵のユニット 1 体に 2 と、ほかの敵のユニットに 1、Mind は 1 枚引く、Order は、敵のユニットをスタンさせる）。
- **動くカード**: 249 → **250 枚**。
- **レビューで直したこと**: Order の「敵のユニットをスタンさせる」は、場所を限らない（Fury は、「ここ」に限る）。リサイクルした Rune が、Rune Deck の一番下へ行くことも、テストで確かめる。
- **近似として残したこと**: ほかの領域の Rune が出たときは、何も起きない（カードの文面にも、書かれていない）。

### M7 の実装の記録（2026-11-23）: デッキの上から、ユニットをプレイする（2 枚）

- **エンジン**: `Prim.playFirst`（デッキの上から、条件に合うカードが出るまで、めくる。それを、費用を払わずにプレイし、めくった、ほかのカードは、リサイクルする。合うカードがなければ、デッキの全部をリサイクルする）。
- **動くようになったカード**: Reinforce（062。上の 5 枚を見て、Energy が 5 以下のユニットを 1 枚、プレイしてもよい。残りは、好きな順で、リサイクルする）、Dazzling Aurora（160。自分のターンの終わりに、`playFirst`）。
- **動くカード**: 247 → **249 枚**。
- **レビューで足したこと**: Reinforce は、上の 5 枚の外にあるユニットを、プレイしない。上の 5 枚に、費用の高いユニットと低いユニットがあるとき、費用の低いほうだけを、選べる。`playFirst` は、ユニットとギアだけを、プレイできる。
- **近似として残したこと**: Reinforce の「費用を 5 減らす」は、Energy が 5 以下のユニットだけを選べて、Power は払わない。Reinforce は、banish してからプレイするのではなく、そのまま、プレイする（banish の出来事は、出ない）。

### M7 の実装の記録（2026-11-23）: 誘発の条件が、見ている物体を使う（1 枚）

- **エンジン**: ほかの物体を見ている誘発の条件は、見ている物体を、スロット 0 として使える（`condOkEnv`。型の検査も、スロットを 1 つ認める）。
- **動くようになったカード**: Volibear, Imposing（158。相手が、自分のいる Battlefield とは別の Battlefield へ移動したとき、1 枚引く）。
- **動くカード**: 246 → **247 枚**。

### M7 の実装の記録（2026-11-23）: 見ている物体を、能力のスロットに渡す（2 枚）

- **エンジン**: ほかの物体を見ている誘発（`PendTrigger.subject`）は、見ている物体を、能力の最後のスロットにして、Chain に載る。選ぶものがなければ、`.slot 0` で指せる。`TriggerEvent.ready`（物体が、準備完了になった）。
- **動くようになったカード**: Pirate's Haven（143。味方のユニットを準備完了にしたとき、そのターン、+1 Might）、Nine-Tailed Fox（255。敵のユニットが、自分が支配する Battlefield を攻撃するとき、そのターン、-1 Might（下限 1））。
- **動くカード**: 244 → **246 枚**。
- **レビューで直したこと**: 「準備完了になった」の出来事は、疲労していた物体にだけ出る。Awaken で準備完了になる物体にも、出る。
- **近似として残したこと**: Nine-Tailed Fox の「自分が支配する Battlefield を攻撃する」は、「自分が支配し、敵のユニットがいる Battlefield がある」で判断する。

### M7 の実装の記録（2026-11-23）: 相手が、カードをプレイできない（1 枚）

- **エンジン**: `TurnEffect.opponentsCantPlay`。ターンの効果が働いているあいだ、そのプレイヤーの相手は、カードをプレイできない（`playable`・`castable` が見る）。
- **動くようになったカード**: Brynhir Thundersong（026）。
- **動くカード**: 243 → **244 枚**。
- **近似として残したこと**: Hidden にするのと、Hidden から使うのは、止めない。効果で、カードをプレイするのも、止めない。起動能力は、止めない（プレイではないため）。

### M7 の実装の記録（2026-11-23）: ボーナスダメージ（2 枚）

- **エンジン**: 効果の「ダメージを与える」は、ダメージ 1 回ごとに、ボーナスダメージを足す（`GameState.bonusOn`）。足すのは、次のスペルのためのターンの効果（`TurnEffect.nextSpellBonus`。作られたあとに、最初にプレイされたスペル）と、対象のユニットがいる Battlefield のパッシブ（`StaticMod.bonusDamageHere`）。戦闘のダメージには、足さない。
- **動くようになったカード**: Ravenborn Tome（032）、Void Gate（296）。
- **動くカード**: 241 → **243 枚**。
- **近似として残したこと（Hidden）**: Hidden から使うスペルは、「次のスペル」として数えない（Tome の効果を使わず、ボーナスも受けない）。Void Gate の効果は、受ける。
- **近似として残したこと**: Ravenborn Tome の「次のスペル」は、そのスペルが与えるダメージだけに効く（そのスペルが起こした別の能力のダメージには、効かない）。

### M7 の実装の記録（2026-11-23）: ダメージを受けたら殺す（2 枚）

- **エンジン**: `TurnEffect.killOnDamage`（このターン、ダメージを受けたユニットは、殺される）。ターンの記録は、物体を指せる（`TurnFx.target`・`Prim.markOn`）。`dealObj` は、記録を見て、ダメージを与えたあとに、殺す（効果のダメージも、戦闘のダメージも、ここを通る。ダメージが 0 のときは、殺さない）。
- **動くようになったカード**: Imperial Decree（221。すべてのユニットが対象）、Noxian Guillotine, Darius（254。選んだユニットが、次にダメージを受けたときに殺す。Legion なら、今すぐ殺す）。
- **動くカード**: 239 → **241 枚**。
- **近似として残したこと**: 「ダメージを受けたら殺す」は、遅延誘発を Chain に載せず、ダメージを与えるのと同時に、殺す（応答の余地はない）。戦闘のダメージも、同じ関数を通る（テストで確かめた）。

### M7 の実装の記録（2026-11-23）: 今ターンに起きたことを、ゲームに残す（2 枚）

- **エンジン**: ユニットが殺されたとき（死んだときの controller）と、カードが捨てられたとき（持ち主）は、ターンの記録（`turnFx` の `unitDied`・`cardDiscarded`）に残る（`killObj`・`discardObj`・手札の上限による捨て札）。`Condition.enemyUnitDied`・`Condition.discardedThisTurn`。記録は、墓地にあるかどうかに、よらない（トークンも、墓地を離れたカードも、数える）。
- **動くようになったカード**: Spoils of War（144。敵のユニットが死んでいると、費用が 2 減る）、Raging Soul（019。カードを捨てていると、Assault と Ganking を持つ）。
- **動くカード**: 237 → **239 枚**。
- **近似として残したこと**: 殺された Unit だけを数える（Gear は、数えない）。

### M7 の実装の記録（2026-11-23）: 条件つきの、Add の能力（1 枚）

- **エンジン**: Add の能力（Energy や Power を足す能力）の効果は、`.ifThen 条件 (Add) .nop` の形でもよい。条件が成り立たないときは、使えない（`manaReady` が `guardOk` を見る）。
- **動くようになったカード**: Hand of Noxus（253。Legion: ほかのカードをプレイしたあとだけ、Energy 1 を足す）。
- **動くカード**: 236 → **237 枚**。
- **レビューで直したこと**: Add の条件は、わかる条件のときだけ、「動く」と数える。テストは、実際のプレイ、古いターン、相手のプレイ、疲労済みも確かめる。
- **近似として残したこと**: 条件が成り立たないときは、疲労させるだけの起動も、できない。

### M7 の実装の記録（2026-11-23）: 追加の費用（払ったあとで、減らした分を Pool へ戻す）、6 枚

- **エンジン**: `Prim.addEnergy`・`Prim.addPower`（効果で、Pool へ、Energy と、領域つきの Power を足す。使い道の制限つきは、まだ）。
- **動くようになったカード**: Brazen Buccaneer（002。カードを 1 枚捨てると、Energy 2 を戻す）、Wallop（146）と Call to Glory（207）（バフを消費すると、費用を戻す）、Kraken Hunter（150。バフを消費するごとに、Body 1 を戻す）、Cruel Patron（208。味方のユニットを 1 体殺す。ほかにいなければ、自分が死ぬ）、Commander Ledros（231。味方のユニットを何体か殺すと、1 体ごとに、Order 1 を戻す）。
- **動くカード**: 230 → **236 枚**。
- **レビューで直したこと**: 戻す量は、払った量を超えない（`Object.energyPaid`・`Amount.energyPaid`。無料でプレイしたカードは、戻さない。Kraken Hunter と Commander Ledros は、数えた数と、費用の Power の数の、小さいほう）。
- **近似として残したこと**: Wallop と Call to Glory は、先に全額を払える Pool がないと、プレイできない（打ち消されると、戻しが失われる）。Cruel Patron は、殺すユニットがないと、自分が死ぬ（本来は、プレイできない。`runs` には数えている）。戻した Power は、Rune を戻すのではなく、Pool に入るだけで、フェーズの終わりに消える。
- **近似として残したこと**: 追加の費用は、払ってから戻す（払えるだけの Pool がないと、プレイできない。戻した分は、そのフェーズの終わりに消える）。Cruel Patron は、殺すユニットがないと、自分が死ぬ（本来は、プレイできない）。

### M7 の実装の記録（2026-11-23）: ターン中の移動の回数（2 枚）

- **エンジン**: ユニットが、標準の移動をした回数を、ターンごとに数える（`Object.moves`・`movesTurn`。`moveUnitOf` が数える）。`Amount.movesThisTurn`。`StaticMod.noDamage`（パッシブで、ダメージを受けない。`dealObj` が読む。戦闘ダメージも、ここを通る）。
- **動くようになったカード**: Yasuo, Windrider（205。ターンの 3 回目の移動で、1 点）、Kayn, Unleashed（189。2 回移動したあとは、ダメージを受けない）。
- **動くカード**: 228 → **230 枚**。
- **レビューで直したこと**: 効果による移動（`sendToBf`）も、数える（カードを、Battlefield へプレイするときは、数えない）。場を離れる（ゾーンをまたぐ）と、数え直す。
- **近似として残したこと**: 基地への、効果による移動は、数えない。`dealObj` は、`noDamage` の持ち主が、場にいるかを、見ない。

### M7 の実装の記録（2026-11-23）: Vayne, Hunter（1 枚）

- **エンジン**: `Filter.controlledByOpponent`（相手が支配している Battlefield）。
- **動くようになったカード**: Vayne, Hunter（035。相手が Battlefield を支配していると、準備完了で入る。征服したとき、Energy 1 を払って、手札へ戻ってもよい）。
- **動くカード**: 227 → **228 枚**。

### M7 の実装の記録（2026-11-23）: 効果の途中で、Rune Pool から払う（2 枚）

- **エンジン**: `Prim.pay`（Rune Pool から、Energy と Power を払う。払えるときだけ）と `Condition.canPay`。効果の途中で Pool が変わるので、`SameMeta` は、Pool の変化を許す（物体を動かしても Pool が変わらないことは、`MoveSpec.pools` が受け持つ）。`Prim.playTo` は、選んだカードをプレイできる。
- **動くようになったカード**: Flame Chompers（006。捨てられたとき、Fury を払ってプレイしてもよい）、Ava Achiever（107。攻撃するとき、Mind を払って、Hidden を持つカードを手札から、ここへプレイしてもよい）。
- **動くカード**: 225 → **227 枚**。
- **レビューで直したこと**: `playFree` は、ユニットとギアだけを、基地へ入れる（スペルは、動かさない）。Ava は、Hidden を持つ、スペルでないカードが手札にあるときだけ、払う。
- **近似として残したこと**: 払うのは、そのときの Pool にあるものだけ（払うために Rune を使う、という操作は、効果の途中では、できない。先に Pool へ入れておく必要がある）。

### M7 の実装の記録（2026-11-23）: 既存の部品で書けた 3 枚（エンジンの変更なし）

- **動くようになったカード**: Albus Ferros（230。バフを持つ自分のユニットごとに、「消費するか」を聞いて、消費したら、疲労した Rune を 1 つ引く）、The Candlelit Sanctum（291。上の 2 枚を、それぞれ、リサイクルしてもよい。残りを戻す順番は、選べない）、Fortified Position（279）。
- **動くカード**: 222 → **225 枚**。
- **レビューで直したこと**: Albus は、提示された時点で、そのユニットがバフを持つかを確かめる。Sanctum のテストは、相手が征服したときに、相手のデッキが動くこと（Battlefield の能力は、征服した側のために働く）と、守り切ったとき（Hold）には、動かないことを確かめる。
- **近似として残したこと**: Fortified Position の Shield 2 は、「この戦闘のあいだ」ではなく、「このターンのあいだ」続く（戦闘の長さの持続が、まだない）。Sanctum は、残すカードの順番を選べない。

### M7 の実装の記録（2026-11-23）: 最高の Might による値引き、2 枚目のプレイ、バフの上乗せ（3 枚）

- **エンジン**: `Amount.highestMight`（選んだ物体の、最高の Might。費用の計算で読む）、`Amount.cardsPlayed`（このターンにプレイしたカードの枚数。プレイし直したカードは、1 枚と数える）、`TurnEffect.buffsExtraMight`（このターン、バフが、さらに +1 Might を与える）。費用の引き算（`costCuts`）は、パッシブの Might を読む（`Amount.evalS`）。
- **動くようになったカード**: Sky Splitter（014）、Darius, Trifarian（027）、Stand United（053）。
- **動くカード**: 219 → **222 枚**。
- **レビューで直したこと**: バフの Might（`GameState.buffBonus`）は、`mightNow` も `Filter.might`・`lethal`・`mighty` も、同じものを読む。「バフが、さらに +1」の効果は、重なると足される。
- **近似として残したこと**: Darius の「2 枚目」は、自分自身のプレイも数える。同じカードを戻してプレイし直しても、1 枚と数える。1 回の処理で複数のカードがプレイされると、その途中の枚数は、見ない（最後の枚数で判断する）。

### M7 の実装の記録（2026-11-23）: 条件つきの「準備完了で入る」と、Might の下限（3 枚）

- **エンジン**: `Amount.victoryScore`（モードの勝利点。パッシブによる増減は、含まない）。`GameState.readyNow`（カード自身の、条件つきのパッシブ。場にある、自分のオブジェクトのパッシブ。ターンの効果）が、「準備完了で入る」を決める（`StaticMod.entersReady` は、選択子つきで動く）。パッシブの `mightMinusMin`（下限つき）は、ほかの変化のあとに読む（`modFloor`・`mightNow`）。
- **動くようになったカード**: Find Your Center（047。相手の得点が勝利点まで 3 以内なら、費用が 2 減る）、Magma Wurm（011）、Leona, Zealot（079）。
- **動くカード**: 216 → **219 枚**。
- **レビューで直したこと**: 「準備完了で入る」の側は、パッシブの持ち主から見て決める（全員に効くパッシブは、相手のユニットにも効く）。`Amount.victoryScore` は、条件のないパッシブによる増減（Aspirant's Climb）を含む。
- **近似として残したこと（相手）**: 「an opponent」は、1 対 1 の相手（`PlayerSel.opponent`）で書いてある。トークンは、`readyNow` を通らない。下限つきの引き算は、ほかの引き算のあとに読む（規則は、時刻順）。`Filter.might`・`lethal`・`mighty` は、パッシブを読まない。
- **近似として残したこと**: 下限つきの引き算が複数あると、書いた順に引く。「準備完了で入る」のパッシブは、その持ち主がプレイするカードにだけ効く。

### M7 の実装の記録（2026-11-23）: 打ち消し（Chain の上のスペルを選ぶ）、3 枚

- **エンジン**: `Place.onChain`（Chain の上のスペル。自分自身と、能力は含まない）。選ぶ対象が、盤面か Chain の上のスペルになった（`mem_candidates`・`targetsOk_mem_inPlay`・`castable_targets_inPlay` の主張を、「盤面、または Chain の上のスペル」に広げた。`.slot` も同じ）。`Prim.counter`（スペルを、解決せずに、持ち主の Trash へ送る）。
- **動くようになったカード**: Defy（045。費用の上限は、Energy 4 と Power 1）、Wind Wall（064）、Stormbringer, Volibear（250）。
- **動くカード**: 213 → **216 枚**。
- **レビューで足したこと**: 負のテスト（Chain が空、自分自身は対象にできない、Stormbringer の第 1 対象は、基地の味方ユニット）。
- **近似として残したこと**: Defy の費用の上限は、カードに印刷された費用で見る（払った費用ではない）。Mystic Reversal（080。スペルの支配を奪う）は、まだ。

### M7 の実装の記録（2026-11-23）: ターンの終わりまで続く効果（4 枚）

- **エンジン**: `GameState.turnFx`（誰の・どのターンの・そのとき何枚プレイしていたか・何の効果か）。新しい `Prim.turnEffect`（`TurnEffect`: 次のスペルの費用を n 減らす・次のユニットが準備完了で入る・このターンのユニットが準備完了で入る・スペルと能力がダメージを与えない）。「次の」は、記録した枚数のあとにプレイした同じ種類のカードがないことで判断する（使い終わった印は、付けない）。ターンが変わると、効くものがなくなる。`SameMeta` は、`turnFx` の変化を許す。`GameState.readyNow`（カードの「準備完了で入る」か、効果による）が、プレイするときの疲労を決める。`costCuts` は、効果による「次のスペル」の割引を読む。`Condition.playedAnother`（能力を使うときに、ほかのカードをプレイ済み）が動く。
- **動くようになったカード**: Sun Disc（021）、Raging Firebrand（031）、Confront（129）、Unyielding Spirit（145）。
- **動くカード**: 209 → **213 枚**。
- **レビューで直したこと**: 「次の」は、カードの `playedStamp`（プレイしたときのタイムスタンプ。ゾーンを移っても変わらない）が、効果を作ったときより新しいカードがないことで判断する（プレイし直したカードも、数える。死んだり戻ったりしたカードは、数えない）。
- **近似として残したこと**: Unyielding Spirit は、スペルと能力のダメージだけを止める（戦闘ダメージは、止めない）。Sun Disc の Legion は、能力を使うとき（「ほかのカードをプレイ済み」でないと、使えない）。

### M7 の実装の記録（2026-11-22）: 墓地から無料でプレイする、ほか 9 枚

- **エンジン**: `play`（選んだカードを、費用を払わずにプレイする）は、墓地・盤面など、どこからでも選べる（`pickSel?` に加えて、選択を聞く）。`Filter.cost`（Energy の費用）と `Filter.powerCost`（Power の個数）が動く。Rune は、Rune Deck の下へリサイクルされる（`recycleKind`）。**墓地へ送られたカードは、送られる前の場所（`loc`）を覚えている**（死んだときの効果の「ここ」が、死んだ場所を指す）。
- **動くようになったカード**: Meditation（048）、Party Favors（071）、Portal Rescue（102）、Thousand-Tailed Watcher（116）、Kog'Maw（190）、Soulgorger（196）、The Harrowing（198）、Spectral Matron（226）、Sigil of the Storm（287）。
- **動くカード**: 200 → **209 枚**。
- **レビューで直したこと**: `playFree` は、盤面にいるユニットを選ぶと、ダメージ・バフ・場所などを消した新しい物体として、基地に入る（すでに基地にいても、その場でプレイし直す）。`Filter.cost` は、費用のないカードを、「当てはまらない」とする。
- **近似として残したこと（人数）**: Party Favors の「each other player」は、`PlayerSel.opponent`（1 対 1 の相手）で書いてあり、3 人以上は考えない。Soulgorger・The Harrowing・Spectral Matron は、Power を払わない（`runs` には数えている）。
- **近似として残したこと**: 「Energy の費用を無視して（Power は払う）プレイする」は、Power も払わない。Portal Rescue は、追放せずに、そのまま基地へプレイし直す（追放の出来事は出ない）。Meditation の「追加の費用として、ユニットを疲労させる」は、解決のときに払う（払えないときは、選べない）。

### M7 の実装の記録（2026-11-22）: 費用の変更（カードの費用を、プレイするときの値にする）

- **エンジン**: カードをプレイする費用（`GameState.effCost`）は、印刷された費用から、**パッシブ能力の `costMinus`・`costMinusMin`（最低値つき）**を引いたものになる。プレイできるか・払う額・追加の費用を払ったかが、これを読む（`playable`・`castable`・`applyPlay`・`applyCast`・`legalPlays` と、`paidExtra`）。引く能力は、場にあるものと、カード自身（手札にいても働く）の、条件が成り立つもの。Legion の条件は、「このターンに、ほかのカードをプレイした」で判断する。選択子の「味方」は、能力を持つ物体の controller から見る。
- **書いた・動くようになったカード**: Noxus Hopeful（012）、Eager Apprentice（084）、Herald of Scales（140）、Rhasa the Sunderer（195。すでに書いてあったが、エンジンが読んでいなかった）。
- **動くカード**: 196 → **200 枚**。
- **レビューで直したこと**: Legion は、プレイするカード自身を、数えない（同じターンに、プレイして手札へ戻したカードも）。費用を引く能力は、「カード自身」か、「どこにいても」の選択子だけを、動くものに数える。
- **近似として残したこと（順序）**: 規則（356）では、追加費用を足してから、割引と最低値をかけるが、実装は、基本の費用に割引と最低値をかけてから、追加費用（Accelerate など）を足す（割引が大きいときや、最低値が効くときに、値が変わる。該当するカードは、まだ無い）。最低値の違う割引が複数あると、並び順で値が変わる。費用の増加（`costPlus`）は、まだ無い。
- **近似として残したこと**: 費用の引き算は、Energy だけ（Power は変わらない）。引く能力が複数あるときは、書いた順に引く。Sky Splitter（最高の Might）、Find Your Center（得点の差）、Spoils of War（このターンに敵の Unit が死んだ）は、まだ。

### M7 の実装の記録（2026-11-22）: デッキの上の n 枚、Battlefield の攻撃・防御の誘発

- **エンジン**: フィルタ `top n`（持ち主の Main Deck の上から n 枚の中）、数 `costOf`（選んだカードの Energy 費用）、プリミティブ `reveal`（見せる。何も変えないが、選ぶ）。**Main Deck のカードを Recycle する**と、同じゾーンのまま一番下へ回る（`recycleOne`）。**Battlefield の誘発**: 戦闘が始まるとき、そこで攻撃・防御するプレイヤーのために、Battlefield 自身の `attack`・`defend` の能力が働く。
- **書いた 6 枚**: Get Excited!（008）、Stacked Deck（183）、Fading Memories（180。`eitherOf` で、Unit か Gear を選ぶ）、Pack of Wonders（181）、Hidden Blade（213。殺される Unit の controller が 2 枚引く）、Reaver's Row（285）。変異で、テストが落ちることを確かめた。
- **動くカード**: 190 → **196 枚**。
- **レビューで直したこと**: 選んだ手札のカードを捨てる動作 `discardCard`（「捨てた」出来事が出る。Scrapheap の誘発が働く）。Get Excited! と Mindsplitter は、これを使う。Get Excited! のテストは、費用と Might が違うカード、空の手札、Scrapheap の誘発を確かめる。Hidden Blade は、Unit が死ぬことを確かめる。
- **近似として残したこと**: Fading Memories の選択肢は、成り立つかを見ずに選べる（Unit がなければ、「はい」で何も起きない）。Hidden Blade の引くことは、死ぬことの前に起きる。Pack of Wonders の 3 つの選択は、「はい」「いいえ」の順に聞く。Pack of Wonders の 3 つの選択は、「はい」「いいえ」の順に聞く。

### M7 の実装の記録（2026-11-22）: 「バトルフィールドへプレイする」と、相手の手札・伏せたカードを選ぶ

- **エンジン**: プリミティブ `playTo`（費用を払わずにプレイして、Battlefield へ移す）。「〜へプレイしてもよい」は、手札から使う起動型能力（`fromHand`、費用はカードの費用）で表す。フィルタ `openBf`（誰も支配していない Battlefield）、`enemyOccupied`（相手の Unit がいる Battlefield）。場所 `inHidden`。`bin`（Trash へ）も、解決中に選べる。相手の手札を選ぶ（`enemy inHand`）。
- **書いた 8 枚**: Sai Scout（174）、Sneaky Deckhand（176）、Deadbloom Predator（161）、Sabotage（156）、Mindsplitter（192）、Mushroom Pouch（101）、Sona（073。4 つの Rune を Ready にする）、Ekko（110。死んだら、自分を Recycle して、Rune を Ready にする）。4 つの変異で、テストが落ちることを確かめた。
- **動くカード**: 182 → **190 枚**。
- **レビューで直したこと**: バトルフィールドへプレイしても、移動の出来事は出ない（「移動したとき」の誘発が働かない）。Sai Scout の Vision、Predator が置かれる場所と、自分の Unit だけの Battlefield は選べないこと、Sona がちょうど 4 つ・自分のターンだけ、Mushroom Pouch が自分の伏せたカードだけ、Ekko が自分の Rune だけ、のテストを足した。
- **確かめられていないこと**: `openBf`（誰も支配していない Battlefield）が、規則の「空いている Battlefield」と同じか。効果の解決時に、対象が不正になっても、起動型能力は、そのまま働く（エンジン全体の制約）。Ekko の「自分を Recycle」は、Trash にいるかを確かめない。
- **近似として残したこと**: 「プレイする」ことが、起動型能力（Chain を使う）で行われる。相手の手札を「公開する」ことは、情報の公開なので、何も起きない。Mindsplitter の「捨てる」は、Trash へ送るだけで、「捨てた」出来事は出ない。「相手を選ぶ」は、2 人戦で相手が 1 人。

### M7 の実装の記録（2026-11-22）: 「費用」を、解決のときの効果で表す

- **エンジン**: プリミティブ `spendBuff`（選んだ Unit の Buff を、使って、失わせる）。起動型能力・誘発の、「Recycle する」「Buff を使う」「これを Kill する」という費用を、**解決のときの効果の最初**に置いて表す。費用が払えないときは、効果の全体を、何もしない（`ifThen`）。
- **書いた 7 枚**: Vi（036）、Garbage Grabber（099）、Sett（164）、Forge of the Future（212）、Monastery of Hirana（282）、Wildclaw Shaman（147）、Overt Operation（153）。変異で、テストが落ちることを確かめた。
- **動くカード**: 175 → **182 枚**。
- **レビューで直したこと**: 効果の先頭が `ifThen 条件 …` の起動型能力は、**起動するときにも、その条件が成り立っていること**を求める（`guardOk`。費用が払えない能力は、起動できない。空の Trash の Vi を、無限に起動することはできない）。Overt Operation は、Buff のある Unit にだけ、使うかを聞く。
- **近似として残したこと**: 費用の支払い（Recycle する、Buff を使う、Kill する）は、起動したときでなく、**解決したとき**に行う（相手が応答で、材料を変えられる。起動後に材料が揃う、起動後に材料が消える、という差がある）。「Kill this」の Forge は、起動してから解決までの間、まだ場にいて、応答で手札へ戻されると、盤の外の物体が「死ぬ」ことになる。

### M7 の実装の記録（2026-11-22）: Hidden（伏せる）

- **エンジン**: キーワード **Hidden**（CR 811）を、2 つの起動型能力で表した。(1) **Hide**: 手札から、Power 1 つ（どの領域でもよい）を払い、自分が支配する Battlefield へ、伏せて置く（`fromHand`、効果 `hideAt`）。(2) **伏せたカードをプレイする**: 伏せた次のターンから、Reaction として、費用を払わずに（`fromHidden`）。Unit と Gear は、Base へ出る（`play`。「プレイしたとき」の誘発が働く）。呪文は、効果をして、Trash へ行く（`bin`）。新しいゾーン `hidden`、物体の記録（`hiddenAt`・`hiddenTurn`）、能力を使える場所の判定（`abilityZoneOk`）を足した。Hide とプレイは、既存の起動型能力と Chain の仕組みを使うので、新しい行動の種類は要らず、証明は、`Chain.lean` の数か所だけで通った。
- **書いた・動くようになったカード**: Block、Consult the Past、Sprite Call、Blastcone Fae、Pakaa Cub、Fight or Flight、Teemo（Scout）、Facebreaker（新しく書いた。2 つ目の選択は、1 つ目と同じ Battlefield の敵）。変異（Hide の費用・Battlefield の支配）で、テストが落ちることを確かめた。
- **動くカード**: 167 → **175 枚**。
- **レビューで直したこと**: 伏せたカードのプレイ能力は、Chain に載っている間に、もう一度使えるので、解決のときに「まだ伏せてある」ことを確かめる（呪文の効果が 2 回走らない）。Hide は、解決のときに、手札にあって、自分が支配する Battlefield であることを確かめる。手札・伏せたカードの、ふつうの起動型能力が、使えないことのテストを足した。
- **近似として残したこと**: Hide・伏せたカードのプレイが、Chain を使い、応答される（規則では、Chain を使わないかもしれない）。伏せた呪文は、能力として働くので、「呪文をプレイしたとき」の誘発が働かず、打ち消せない。Unit と Gear は、Base へ出る（Hide した Battlefield へ出るかは、未確認）。1 つの Battlefield に伏せられる枚数の上限は、後から足した（Bandle Tree の記録を見よ）。伏せたカードの Battlefield を、支配していない人のものになったら、Trash へ送る規則（323.6.a）は、まだ無い。Hidden のカードを「伏せたカードから、プレイした」ときの誘発（Ember Monk、Teemo の Strategist）と、Hide の費用を変える能力（Swift Scout）は、まだ無い。

### M7 の実装の記録（2026-11-22）: 勝つために要る点数の変更、相手に選ばせる

- **エンジン**: 勝つために要る点数（`GameState.victoryScore`）が、パッシブ能力の増減（`victoryScorePlus`・`victoryScoreMinus`）を含む。勝者の判定・Hold の最後の 1 点の規則・「勝つ」の効果が、これを読む。`eachPlayer .opponent` と `eitherOf` で、「相手に選ばせる」文を書ける。
- **書いた 3 枚**: Aspirant's Climb（276。すでに書いてあったが、エンジンが読んでいなかった）、Shakedown（033。相手が、2 枚引かせるか、6 ダメージを受けるかを選ぶ）、Spirit's Refuge（063。Buff された味方に Deflect。もともと持つものには、足さない）。
- **動くカード**: 164 → **167 枚**。
- **近似として残したこと**: Spirit's Refuge の「もともと持たなければ」は、印刷されたキーワードで判断する。
- **既知の制限（レビューで見つかったこと）**: Spirit's Refuge は、**ほかのパッシブで Deflect を得ている Unit**（Mighty の Fiora など）にも足す（Deflect 1 が 2 になる）。Shakedown は、相手が複数いるとき、「対象の controller」でなく、先頭の相手に尋ねる（2 人戦では正しい）。勝つために要る点数が下がって、すでに足りているときは、次の Cleanup で勝つ。

### M7 の実装の記録（2026-11-22）: 「最大 2 つ」「2 つの」を、異なる 2 つを選んで表す

- **エンジン**: `grant`（一時的な変更）も、対象を解決中に選べる。2 つ目の選択は、`not (sameAs (var pickVar))` で、1 つ目と違う物を選ぶ（1 つ目を選んだ後の変数を、候補の計算が読む）。
- **書いた 3 枚**: Singularity（105。最大 2 つの Unit に 6 ダメージ）、Kinkou Monk（141。ほかの味方を最大 2 体 Buff）、Back to Back（206。2 体の味方に +2）。2 つ目の選択が、1 つ目と同じ物にならないことを、変異で確かめた。
- **動くカード**: 161 → **164 枚**。
- **近似として残したこと**: 「最大 2 つ」は、1 つ目を選ばなければ、2 つ目も選べない。
- **近似として残したこと（対象）**: 3 枚とも、規則では「対象を選ぶ」文だが、解決のときに選ぶ。そのため、Deflect の追加費用・対象にならないこと・対応で対象が不正になることが、効かない。2 つの対象は、同時でなく、1 つずつ選ぶ。Back to Back は、Unit が 0 体・1 体でも唱えられる（規則では、対象が足りなければ、唱えられない）。cast 時に 2 つ以上の対象を取ることは、まだ無い。

### M7 の実装の記録（2026-11-22）: 「どちらかを選ぶ」（`chooseOne`）

- **エンジン**: 効果 `eitherOf`（解決のときに、どれかを選ぶ。プレイ時に選ぶ `chooseOne` とは別）を、解決のときに、プレイヤーに聞く決定として足した（フレーム `eitherDo`。「する」が最初のモード、「しない」が残り。3 つ以上は、順に聞く）。証明は、`mayDo` の腕と同じ形を、7 つの不変条件に足して通した。フィルタ `sameAs`（選んだ物体と同じ）も足した。`pickVar`（解決中に選んだ物体）は、あとの文でも使える。
- **書いた 5 枚**: Qiyana（155。引くか、Rune を Exhaust で Channel するか）、Charm（043）、Ride the Wind（173）、Unforgiven（259。Legend）、Dragon's Rage（258。移動し、行き先にいる別の敵と、Might に等しいダメージを与え合う）。移動は、Base か、選んだ Battlefield へ。5 つの変異で、テストが落ちることを確かめた。
- **動くカード**: 156 → **161 枚**。
- **レビューで直したこと**: Unforgiven は、Battlefield の Unit は Base へだけ、Base の Unit は選んだ Battlefield へだけ動かす。Dragon's Rage は、行き先に別の敵がいないとき、動かした Unit にダメージを与えない。
- **まだ無いこと**: 進行中の Combat がある Battlefield へは移動できない規則（CR 449.2.a）は、まだ無い（Charm・Ride the Wind・Dragon's Rage が、実際に当たる）。3 つ以上の `eitherOf` の入れ子は、カードにもテストにも、まだ無い。
- **近似として残したこと**: 「どちらかを選ぶ」は、プレイ時でなく、解決時に選ぶ（対象を選んだ後）。

### M7 の実装の記録（2026-11-22）: 「そうでない」フィルタ、得点の数、Recycle

- **エンジン**: フィルタ `not`、数 `points`（プレイヤーの得点）、プリミティブ `recycle`（選んだカードを、持ち主の Main Deck の一番下へ。解決中に選べる。Trash から選べる）。「そのターンの最初の 1 回」は、すでにあった `perTurn 1` の制限で表せる（誘発した能力が、使われたことを記録する）。
- **書いた 6 枚**: Wraith of Echoes（118）、Miss Fortune（162）、Viktor（246）、Draven（028。Might が、自分の得点だけ増える）、Relentless Storm（249。Legend）、Dr. Mundo（109。Trash の枚数で Might が増え、Beginning Phase の始めに 3 枚 Recycle する）。6 つの変異で、テストが落ちることを確かめた。
- **レビューで直したこと**: 1 回のステップで、同じ誘発が複数回起きても、`perTurn` の制限を超えないように絞る（`trimLimits`。Wraith が、同時に 2 体死んでも、1 枚だけ引く）。2 体の Wraith は、それぞれ引く。選ぶ Recycle の選択、相手の Beginning Phase では働かないことのテスト。
- **既知の制限**: `mighty` は、パッシブの増減を読まない（Draven が Might 5 以上でも、Relentless Storm は、Mighty とは見ない）。Miss Fortune は、Legend を Ready にできない（`anywhere` は、Base と Battlefield だけ）。
- **動くカード**: 150 → **156 枚**。
- **近似として残したこと**: Wraith は、自分が死んだときを見ない（死んだ後は、場にいない）。

### M7 の実装の記録（2026-11-22）: 場所のフィルタ（`at_`）と、移動先の選択

- **エンジン**: フィルタ **`at_`**（「そこにある」: 選んだ Battlefield や、選んだ Unit のいる場所、Base）と、**移動先を解決中に選ぶこと**（`move s (.at_ (.pick .one ..))`）。
- **書いた 5 枚**: En Garde（046。そこにほかの味方がいなければ、もう +1）、Siphon Power（266。選んだ Battlefield の味方 +1、敵 −1）、Last Stand（069。Might を 2 倍にして、Temporary を与える）、Convergent Mutation（108）、Showstopper（270。Buff して、選んだ Battlefield へ移す）。変異で、テストが落ちることを確かめた。
- **レビューで直したこと**: 移動する物体と行き先の両方を解決中に選ぶ形は、動くものに数えない（2 回目の選択が 1 回目を隠すため）。別の Battlefield の Unit が変わらないこと、Might 1 の敵が 1 のままであること、同じ Unit を 2 回選ぶ Convergent Mutation、敵の Unit を Showstopper で動かせないことのテストを足した。
- **近似として残したこと**: Convergent Mutation の「ほかの味方」は、対象として選ぶ（同じ Unit を 2 回選ぶと、何も変わらない）。`at_` は、Unit か Battlefield に使う。
- **動くカード**: 145 → **150 枚**。

### M7 の実装の記録（2026-11-22）: Vision（デッキの一番上を、一番下へ）

- **エンジン**: プリミティブ `recycleTop`（それぞれのプレイヤーが、Main Deck の一番上のカードを、一番下へ Recycle する）と、キーワード **Vision**（プレイしたとき、Main Deck の一番上を見て、Recycle してもよい）。証明は、Reorder の補題（`wf_reorder`・`physIds_reorder`・`ownerOk_reorder`）で通した。
- **動くカード**: 143 → **145 枚**（Jeweled Colossus、Mystic Poro）。Vision を持つが動かないのは、Gemcraft Seer（与えられた Vision）、Sai Scout（空いた Battlefield へプレイ）、Karma（Recycle の誘発）。
- **レビューで足したこと**: 残りの並びが保たれること、相手の Deck が変わらないこと、空の Deck のテスト。`recycleTop` は、物体の識別子を変えず、移動の出来事も出さない（Karma の「Recycle したとき」の誘発を足すときは、注意）。Vision は、`Prim.predict` ではなく、`recycleTop` で表した（規則の文は、「上を見て、Recycle してもよい」）。
- **近似として残したこと**: 「見る」は、情報の公開なので、モデルでは何も起きない。

### M7 の実装の記録（2026-11-22）: 動くカードを増やす（Accelerate、Trash から選ぶ、支配、勝利）

- **Accelerate** は、すでにエンジンが実行していた（追加費用を払うと、Ready で場に出る）ので、動くキーワードに数えた。Origins の Accelerate のカード 10 枚のうち、ほかの能力も動くものが、動くカードになった。Blazing Scorcher のテストを足した。
- **解決中に選ぶことが、盤の外のカードも選べる**ようになった（`pickCandidates`。手札・Trash・Deck）。対象にはならない（`Choice.candidates` は、盤の上だけ）。Cemetery Attendant と Morbid Return（Trash の Unit を手札へ戻す）が動く。
- **効果の「支配を奪う」「Recall」「勝つ」**（`Prim.takeControl`・`recall`・`win`）。勝つことは、Victory Score まで得点することで表し、次の Cleanup が勝者を決める。Possession と The Grand Plaza が動く。
- **動くカード**: 298 枚のうち **143 枚**（133 → 143）。残りの 155 枚のうち、キーワードで止まるのは Hidden（14）と Vision（5）。
- **レビューで直したこと**: 盤の外のカードを選ぶことは、「手札へ戻す」だけを、動くものに数える（ほかの動作は、盤の外を選べない）。支配を奪う・Recall は、解決中に選ぶ形を数えない。Possession が、ダメージ・Ready／Exhausted を保つことと、The Grand Plaza が、敵の Unit・ほかの Battlefield の Unit を数えないことのテストを足した。
- **近似として残したこと**: 「勝つ」は、Final Point の規則を通らない、得点による勝利で表す。「Recall」は、Move の誘発を出さない（規則どおり）。

### M7 の実装の記録（2026-11-22）: 「カードが動く」の測り直し

- **何が分かったか**: これまで数えてきた「書けた（drafted）」は、IR の値として書けたことであり、**エンジンが、書かれた能力を実行する**こととは、別である（例: Rhasa の費用の減少、Karthus の誘発の追加、Possession の支配の奪取は、書いてあるが、エンジンが読まない）。目標は、「第一弾のカードが全て機能する」ことなので、**実際に動くカード**を数え直した。
- **測り方（`CardDef.runs`、`Riftbound/Rules/Understood.lean`）**: カードの能力が、すべて、エンジンが実行できるもの（パッシブの変更、誘発の種類・条件・対象、起動型能力の費用と効果、呪文の効果）であり、キーワードが、すべて、エンジンが知っているもの（Reaction・Action・Assault・Shield・Ganking・Tank・Temporary・Legion・Deflect・Deathknell・Hunt・Level・Equip）であること。`RiftboundTest/Cards.lean` が、Origins の 298 枚のうち、動く枚数を固定している。
- **現状**: **298 枚のうち 133 枚が動く**（書けた 156 枚のうち、動かないのが 23 枚、まだ書けていないのが 142 枚）。動かない原因のうち、キーワードが **Hidden（14 枚）・Accelerate（10 枚）・Vision（5 枚）**。
- **次**: 残りの 165 枚を、効果・キーワードの種類ごとに、1 つずつ動かす。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 12 弾: 効果による移動）

- **エンジン**: 効果の移動（`Prim.move s (.at_ d)`）を足した。行き先は、Battlefield か、物体のいる場所（Unit なら、その Unit のいる Battlefield か Base）。Exhaust せず、行き先を Contested にし、移動の出来事（`standardMoved`）を出す。すでにそこにいれば、何もしない。移動する物体を、解決中に選ぶこと（`Selector.one`）もできる。
- **書いた 2 枚**: Zenith Blade（262。Stun して、味方を、その Battlefield へ移してもよい）、Blitzcrank（067。Battlefield にプレイしたとき、敵の Unit をここへ移してもよい。Hold したら手札へ戻る）。
- **書かなかった（行き先を、プレイヤーが選ぶ）**: Charm、Ride the Wind、Unforgiven、Showstopper、Dragon's Rage。行き先（Base か、どの Battlefield か）を選ぶ決定が要る。
- **レビューで直したこと**: すでに Contested の Battlefield は、Contested にした人を保つ（上書きしない）。行き先が Base にいる Unit のときは、解釈しない（飛ばす）。移動後に、Battlefield が Contested になり、Showdown が始まること、Hold 以外では Blitzcrank が戻らないことのテストを足した。
- **近似として残したこと**: 「Battlefield にプレイしたとき」は、「ここにいる味方の Unit がいる」で近似した（Blitzcrank）。進行中の Combat がある Battlefield へは移動できない規則（CR 449.2.a）は、まだ無い。効果で Base へ移すとき（`.move s .base`）は、移動の出来事が出ない。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 11 弾: ターンの区切りの誘発）

- **エンジン**: 出来事 `Event.phaseStarted`（Awaken・Beginning・Main・Ending の始まり）を足し、**「〜の始めに」「ターンの終わりに」の誘発**（`TriggerEvent.at_`）が、その区切りで働く。働くのは、その区切りのターンのプレイヤーが操る物体（と Legend）の能力と、**Battlefield の能力（ターンのプレイヤーのために働く）**。`Amount.turnsTaken`（そのプレイヤーが取ったターン数。今のターンを含む）も動く。
- **書いた 3 枚**: Loose Cannon（251。Legend。Beginning Phase の始めに、手札が 1 枚以下なら 1 枚引く）、Obelisk of Power（284）と The Arena's Greatest（290。それぞれのプレイヤーの最初の Beginning Phase に、Rune を 1 つ Channel／1 点）。
- **近似として残したこと**: 区切りの誘発は、区切りの始まりに、Chain に載る。Awaken の誘発は、Ready の後になる。Beginning Phase の誘発は、Hold の得点（と Temporary の Kill）の後になる（ルールでは、その前）。Ending Phase の誘発は、ダメージの除去と「このターン」の効果の失効の後になる（ルールでは、その前）。Loose Cannon の「手札が 1 枚以下なら」は、誘発の検出時に判断する（解決時ではない）。Equipment が与える区切りの誘発は、拾わない。
- **副作用**: これまで働かなかった Dark Child（OGS-017。ターン終了時に Rune を 2 つ Ready する）が、働くようになった。ただし、「Rune を 2 つ選ぶ」はまだ解釈できず、その文は飛ばされる（ゲームは止まらない。テストで確かめた）。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 10 弾: 「それぞれのプレイヤーが」）

- **エンジン**: 効果 `Effect.eachPlayer`（それぞれのプレイヤーが、その効果をする）を足した。効果は、そのプレイヤーとして解決するので、選ぶこと（「自分の Unit を 1 体 Kill する」）は、そのプレイヤーのものになる。証明は、そのまま通った。
- **書いた 4 枚**: Acceptable Losses（179）、Cull the Weak（209）、Invert Timelines（201。手札を全部捨てて、4 枚引く）、Whirlwind（187。Unit を 1 体、持ち主の手札へ戻してもよい）。変異で、テストが落ちることを確かめた。
- **レビューで直したこと**: Whirlwind は、2 人戦で「次のプレイヤー（相手）から」の順にした（`eachOpponent` の次に `you`）。相手に Unit・Gear が複数あるときの選択（相手への `pickDo`）、相手の手札を捨てることのテストを足した。
- **近似として残したこと**: Whirlwind の順は、2 人戦だけが正しい（多人数は、手番順の走査が要る）。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 9 弾: 得点、致死ダメージ、盤の外のカードの数）

- **エンジン**: (1) 効果の**得点**（`Prim.score`）。安全な変更の定義（`SameMeta`）が、得点の変化を許すようにした（得点は、`WF` にも、物理カードにも関わらない。証明は、そのまま通った）。(2) フィルタ**`lethal`**（致死ダメージ。0 でなく、Might 以上）。(3) 盤の外の場所（手札・Trash・Main Deck・Rune Deck）にあるカードの**数**（`Amount.count`）。対象にはまだ選べない。
- **書いた 5 枚**: Disintegrate（005。致死なら 1 枚引く。「これで Kill すれば」を、致死ダメージで近似する）、Adaptatron（056。「してもよい」を選び、Kill できたら Buff）、Ahri（066。Hold で 1 点）、Mobilize（134）と Catalyst of Aeons（138。Channel できなければ、引く。Rune Deck の数で判断する）。変異（lethal・gear の有無・数える場所・得点の相手）で、テストが落ちることを確かめた。
- **レビューで直したこと**: Adaptatron は、Gear が無いときは聞かない。Catalyst は、文の順（Channel してから引く）にし、Channel 前の Rune Deck の数を束縛して判断する。得点が 0 のときは、出来事を出さない。Channel した Rune が Exhausted であること、Rune Deck が空の Catalyst、すでにあるダメージ・Buff との合算、自分の Gear、Victory Score への Hold のテストを足した。
- **近似として残したこと**: `lethal` は、パッシブの Might の増減を読まない（Cleanup の判定は読むので、食い違うことがある）。「これで Kill すれば」は、ダメージが致死になったかで判断する（Cleanup で、実際に死ぬ前）。Adaptatron の「If you do」は、「Kill できる gear がある」で近似する。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 8 弾: 戦闘の文脈と、Mighty）

- **エンジン**: 戦闘の文脈（`GameState.combatNow`）を足した。いま進行中の Combat の Battlefield と Attacker を、スタックの戦闘のフレーム（`combatDamage`・`assign`・`combatResolve`）から読む。これで、**場所 `inCombat`**（戦闘中の Unit）と、**フィルタ `attacker`・`defender`・`alone`**（戦闘中に、自分の側でただ 1 体）が動く。**フィルタ `mighty`**（Might 5 以上）も動く。`攻撃したとき`・`防御したとき`の誘発は、自分だけでなく、ほかの物体の見張り（`watchersOf`）も働く。
- **書いた 5 枚**: Wielder of Water（055。1 体で戦うとき +2 Might）、Mask of Foresight（060。味方が 1 体で攻撃・防御するとき +1 Might）、Cannon Barrage（127。戦闘中の敵の Unit に 2 ダメージ）、Kadregrin the Infernal（038。Mighty の味方 1 体につき 1 枚引く）、Fiora（232。Mighty の間、Deflect・Ganking・Shield）。変異（alone・inCombat・mighty の違い）で、テストが落ちることを確かめた。
- **レビューで直したこと**: 戦闘の文脈は、Combat の **Showdown の最中**にも読める（Battlefield に 2 人以上の Unit がいる `showdown` のフレーム）。`mighty` と `Filter.might` は、Equipment の Might も数える（`equipBonus` を Select へ移した）。
- **近似として残したこと**: `mighty` は、パッシブ能力の増減を読まない（パッシブは、フィルタを自分で読むので、循環する）。Combat Cleanup は、致死の Unit を 1 体ずつ殺すので、Wielder of Water のような「1 体のとき」の増減が、先に 1 体が死ぬと変わり、同時に死ぬはずのものが生き残ることがある（未確認）。モデルでは、Showdown の最中に呪文を唱える手が、まだ無い（Showdown のフレームは Pass だけ）。Cannon Barrage は、Priority のフレームがあるときに、唱えられる（テストは、その状態を作って確かめた）。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 7 弾: Stun と Discard の出来事）

- **エンジン**: 出来事に、**Stun された**（`Event.stunned`）と**捨てられた**（`Event.discarded`。Trash での新しい物体）を足した。誘発の種類に `stun` を足し、`detectOne` が、Stun された物体自身と、見張っているほかの物体（`watchersOf`）の誘発を拾う。捨てる決定（`discardPick`）は、捨てられたカードの出来事を出すので、「捨てたとき」の能力が、効果の捨てる動作からも動く。証明は、変更なしで通った。
- **書いた 4 枚**: Eclipse Herald（059。敵の Unit が Stun されたら、自分を Ready し +1 Might）、Radiant Dawn（261。Legend。敵の Unit が Stun されたら、味方を Buff）、Scrapheap（182。プレイ・捨てられた・Kill されたとき 1 枚引く）、Jinx（202。自分が捨てたら、自分を Ready し +1 Might）。変異（Stun の側・Discard の誘発・Discard の側）で、テストが落ちることを確かめた。
- **レビューで直したこと**: 「捨てたとき」の見張り（Jinx）は、1 回の捨てる効果につき 1 回だけ働く（`Event.discarded` が、効果の最後の 1 枚かどうかの `last` を持ち、カード自身の「捨てられたとき」は毎回働く）。ビューアが、Stun された・捨てたの出来事を表示する。
- **近似として残したこと**: 「1 つ以上」の Stun（Radiant Dawn）は、Stun の 1 体ごとに誘発する（複数体を同時に Stun する効果は、まだ無い）。すでに Stun 済みの Unit を、もう一度 Stun しても、出来事が出る。「あなたが Stun する」は、「敵の Unit が Stun される」で近似する（相手の効果が、相手の Unit を Stun しても、働く）。
- **書けなかった**: Pirate's Haven（143。Awaken の Ready の出来事が出ない）、Solari Shrine（072。死んだ Unit が Stun されていたかを、出来事が持たない）、Flame Chompers（006。Trash からプレイする効果がいる）。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 6 弾: Might に応じたダメージと、対象を 2 つ取る呪文）

- **エンジンの変更なし**（第 5 弾の `mightOf` の評価と、2 つの対象の選択だけで書ける）。テストの道具 `payOf` は、「どの領域の Power でもよい」記号（Last Breath の費用）を、Fury で払う。
- **書いた 5 枚**: Poro Herder（061。Poro を持てば、自分を Buff して 1 枚引く）、Solari Chief（225。Stun 済みなら Kill、そうでなければ Stun）、Last Breath（260）、Challenge（128）、Carnivorous Snapvine（149。互いの Might に等しいダメージを与え合う。Snapvine 自身が死ぬことも、テストで確かめた）。
- **レビューで足したこと**: Challenge の与えるダメージ量（生き残る側で確かめる）と、Might 5 同士の相打ち、Poro Herder の否定（Poro でない味方・敵の Poro だけ）のテスト。パッシブの Might の増減の量が `mightOf` のとき、まだ 0 になる（`modMight` は `evalS0`）。
- **近似として残したこと**: 「Challenge」と「Last Breath」の 2 つの対象は、どちらも必須（「いない」ときは唱えられない）。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 5 弾: 攻撃・防御・保持・制圧の誘発と、場所を持つパッシブ）

- **直した 2 つの穴**: (1) 誘発能力の**条件**は、これまで「なし・追加コストを払った・Legion」しか成り立たず、ほかの条件（`yourTurn`、`cmp`、`exists` など）は、**何も言わずに、いつも偽**だった（The Grand Plaza の勝利条件も、実は発動していなかった）。→ `Condition.eval` で評価する（答えられない条件は偽）。(2) 「自分の Might に等しい」（`Amount.mightOf`）は、**評価されていなかった**。→ `Amount.evalS` を、Passive の後ろで、**ルールが読む Might（`mightNow`）**で評価するものに置き換えた（元の評価は `evalS0`。条件の中の `mightOf` は、まだ理解済みに数えない）。
- **テストの道具**: `fire`（出来事を起こし、誘発を Chain に載せて解決する）、`putBf`（Battlefield のカードを置く）、`countNamed`（名前で数える。Recruit トークンなど）。`settleChain` は、捨てる決定も答える。
- **書いた 23 枚**: Leona（238）、Ahri（119）、Anivia（148）、Yasuo（076）、Dune Drake（131）、Grove of the God-Willow（280）、Altar to Unity（275）、Navori Fighting Pit（283）、Startipped Peak（288）、Zaun Warrens（298）、Trifarian War Camp（294）、Windswept Hillock（297）、Darius（243）、Block（057）、Blastcone Fae（097）、Teemo（197）、Fight or Flight（168）、Iron Ballista（017）、Ravenbloom Student（103）、Pit Crew（091）、Viktor（117）、Noxian Drummer（222）、Bounty Hunter（267）。変異で、場所・条件・Might・Ready の 4 つの違いを、テストが検出することを確認した。
- **レビューで直したこと**: Recruit トークンは Exhausted で出す（文に「ready」が無い）ので 3 枚を直し、テストで Exhausted を確かめる。誘発の条件は、**能力が働くプレイヤー（Battlefield なら保持した人）**で評価する（持ち主で評価していた）。Darius の Legion が Ready にすることを確かめる。副作用として、`mightOf` が評価されるので、Gentlemen's Duel（OGS-008）の Might を使う効果が動く。条件つきで、これまで発動しなかった The Grand Plaza・Renekton（VEN-019）が発動するようになった（Renekton のテストは、まだ無い）。
- **近似として残したこと**: Iron Ballista の「Exhausted で場に出る」は、プレイしたときの誘発で、Exhaust する（解決までの間は、Ready のまま。ただし、その間は、Chain が空でないので、通常の起動はできない）。Hidden を持つカードは、Hidden の意味（伏せてプレイ）がまだ無い。Noxian Drummer の「Battlefield へ移動したとき」は、「ここにいる味方の Unit が 1 つ以上ある」で近似した。
- **書かなかった**: Cannon Barrage（127、`inCombat` の場所の評価に、戦闘の文脈がいる）。
- **次の単位**: 起動型能力のほかの費用（Garbage Grabber、Vi、Sett など）か、戦闘の文脈（`inCombat`、`alone`、attacker／defender）。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 4 弾: 「このターン、キーワードを持つ」と、「最小 1 まで」の Might 減少）

- **エンジン**: 物体に、**効果が与えたキーワード（`tempKws`、終わる時点つき）**を持たせた。ターン終了で消え、場を離れても消える。`grantedKws`（戦闘・Deflect・Ganking などが読む）は、**付いている Equipment が与えるもの、パッシブ能力が今与えているもの（`passiveKws`。条件が成り立つときだけ、対象の選択子が物体を指すときだけ）、効果が与えたもの**の 3 つの和になった。これで、「条件つきでキーワードを持つ」（Bilgewater Bully）と、「ここにいるほかの味方が持つ」（Taric、Captain Farron）が動く。
- **Might の「最小 1 まで」**: `StaticMod.mightMinusMin s a floor` を足した。解決のときに、**Might（印刷値＋効果の増減＋Buff）が下限を下回らない分だけ**を引く（`addMightFloor`）。ターン終了に、増減ごと戻る。
- **書いた 7 枚**: Cleave（OGN-004）、Smoke Screen（OGN-093）、Stupefy（OGN-095）、Orb of Regret（OGN-090）、Bilgewater Bully（OGN-125）、Taric（OGN-074）、Captain Farron（OGN-015）。テストは、下限（Might 5・2・1 の 3 通り）、ターン終了での失効、対象外（別の場所・敵）を確かめ、条件・場所・下限を変える 3 つの変異で、テストが落ちることを確認した。
- **書かなかった**: Thousand-Tailed Watcher（OGN-116、Accelerate の意味がまだ無い）、Spirit's Refuge（OGN-063、「もともと Deflect を持たなければ」の否定の条件が要る）、Fiora（OGN-232、「Mighty」は Equipment と パッシブの Might を含む判定が要る。`Filter.mighty` はまだ無い）、Gemcraft Seer（OGN-100、Vision の意味がまだ無い）。
- **レビューで直したこと**: 下限の基準を、印刷値と Buff だけでなく、**ルールが読む Might（`mightNow`。Equipment とパッシブも含む）**にした（Lee Sin の +2 を含む場合のテストを足した）。戦闘でのキーワードの効果（`combatMight`）、手札の Taric は何も与えないこと、同じ Might 減少を 2 回重ねても 1 のままであることのテストを足した。
- **近似として残したこと**: Might の下限は、解決の時点の Might で計算する（あとでほかの減少・増加が起きても、下限は追いかけない）。キーワードを持つ物体を選ぶフィルタは、印刷されたキーワードだけを見る（与えられたキーワードを見ると、循環するため）。Base にいる Taric と Farron は、何も与えない（「ここ」は Battlefield のこと）。
- **次の単位**: 起動型能力のほかの費用（Garbage Grabber など）。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 3 弾: 「〜してもよい」と、解決中に選ぶこと）

- **エンジン**: 効果の途中で、プレイヤーに聞く決定を 2 つ足した。**「〜してもよい」（`Effect.may`）**は、`mayDo` フレームで、「する」「しない」（`decide`）を答える。**解決中に 1 つ選ぶ**（「Kill a gear」のように、プレイ時でなく、解決するときに選ぶ。`Selector.pick .one`）は、`pickDo` フレームで、候補から 1 つ選ぶ（`choose`）。候補が 1 つだけなら、聞かずに、それを選ぶ。候補が無ければ、その文は何もしない。選ばれた物体は、変数 `pickVar` に束縛し、効果の選択部分を `.var pickVar` に置き換えて、実行する。フレームの候補は、`c :: more`（空にならない）で持つので、進行性（I5）の証明は、どの局面でも合法手がある、のまま通る。
- **証明の更新**: 新しい 2 つのフレームと 2 つの答えについて、`applyFrame0` の腕を、7 つの不変条件（WF、物理カード、OwnerOk、手札、スタック、Setup、進行性）と、時計の補題に足した。`runEffect` は、選択を扱う層と、そうでない層（`runEffect1`）に分けた。
- **書いた 4 枚**: Salvage（OGN-224。「Kill a gear」を解決中に選ぶ）、Maddened Marauder（OGN-191。Battlefield の Unit を Base へ）、Zaunite Bouncer（OGN-188。ほかの Unit を持ち主の手札へ）、Clockwork Keeper（OGN-044。追加コストを払えば引く）。
- **ビューア**: 「する」「しない」と、「X を選ぶ」の手が出る。選ぶ手は、盤面のカードをクリックして選べる。
- **レビューで直したこと**: 「理解済み」の判定が、`pick .one` を、どこでも許していた（プリミティブの選択の欄以外では、何も言わずに skip される）→ プリミティブの選択の欄だけに絞った（`Selector.understoodPick`）。Salvage で 2 番目の候補を選ぶテスト、候補が 0 のとき、Bouncer が味方も選べること、Keeper に別の Power は払えないこと、`deal`・`stun`・`buff`・`exhaust` の選択（Play.lean）を足した。
- **近似として残したこと**: Marauder と Bouncer は、プレイ時に対象を選ぶ（`targetOf`。既存の First Mate などと同じ）、Salvage だけが、解決中に選ぶ（`pick`）。Clockwork Keeper の「As you play me」は、「When you play me」の誘発で表した（引くのが解決の後になる。Counter されたとき、引かない）。`Selector.candidates` が分からない場所のとき、候補が無いのと同じに扱う。自動の答え（デモ）は、常に先頭の合法手（`may` は「する」）。
- **書けなかった（今回の対象から外した）**: **Garbage Grabber**（起動の費用に「トラッシュから 3 枚 Recycle」があるが、起動型能力の費用のうち、Exhaust と Energy と Power と自分を Kill だけが支えられている。ほかの費用（Recycle・Discard・Buff を使う・XP を使う・味方を Kill）は、次の単位）。「If you do」（`doThen`）、「choose one」（`chooseOne`）、プレイヤーごとの選択（Cull the Weak など）も、まだ。
- **次の単位**: 起動型能力のほかの費用（Garbage Grabber、Udyr、Sett の Spend a buff など）。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 2 弾: Buff の 6 枚と、ほかの物体の誘発）

- **書いた 6 枚**: Wizened Elder（Buff の間、Might +1）、Sett（OGN-240。自分の Battlefield の Buff 済みの味方 Unit の数だけ Might +1）、Lee Sin（OGN-151。自分の Battlefield の、ほかの Buff 済みの味方に +2）、Arena Bar（exhaust して、exhausted の味方に Buff）、Cithria of Cloudfield（ほかの Unit を play したら、自分に Buff）、Peak Guardian（play したとき、自分に Buff、いる Battlefield のほかの味方にも Buff）。持続する能力は、既存の Passive の仕組みで書けた。
- **エンジン: ほかの物体の誘発**（`watchersOf`）: 誘発する能力は、これまで、物体自身（「When you play me」）だけだった。「When you play another unit」のように、**主語が自分でない能力**を、場の物体と Legend から探して、play・撃破・移動のときに誘発する（主語の側と条件を、そのイベントの物体で確かめる。Spell のように場に無い物体も、主語にできる）。
- **レビューで直したこと**: Arena Bar の速さを `.normal` に（カード文に [Action] が無い）。`subjectHolds` は、主語に場所（`here`、`atBase`）があれば、まだ分からないので、成り立たない（安全側）。否定のテストを足した（敵の play、Spell の play、Lee Sin 自身、基地の Sett）。Peak Guardian の Battlefield での第 2 文は、能力を手でスタックに積んで確かめた（Unit を Battlefield に出す手段がまだ無い）。
- **未対応のまま残したもの**: 「バフ済みの間のキーワード」（Bilgewater Bully、Spirit's Refuge）。キーワードの Passive の条件を、`hasKw` が読まない。ほかの物体の誘発（`watchersOf`）は、Equipment が与える能力と Battlefield 自身の能力を見ない。撃破された物体の主語は、撃破のあとの状態で読む（Buff や exhausted を主語の条件にするカードが出たら、直前の状態を覚える）。誘発の条件 `paid`・`legion` は、監視する側の物体の事実を読む（今の 6 枚は条件が無い）。Filter の `cost` は未実装なので、Lux 系の「コストが 5 以上の Spell」は、まだ誘発しない。

### M7 の実装の記録（2026-11-22）: Origins の全カードへ（第 1 弾: 11 枚とカードラボ）

- **目標**: Origins（298 枚）の全カードを、IR で書き、シナリオテストで動きを確かめる（`drafted` 以上）。1 つの単位は、実装、テスト、レビュー、merge の順。未転記は、この時点で 221 枚（`docs/coverage.md`）。
- **カードラボ**（`RiftboundTest/CardLab.lean`）: 1 枚のカードのシナリオテストを数行で書く道具。第 1 ターンの Main Phase の状態（全セットのカードが分かる）に、カードを置き（`put`、`putAt`）、払える金額を与えて、費用ちょうどで play し（`play`）、Chain を解決させ（誘発の対象は `pick` で選ぶ）、結果を読む。カードがゾーンを移ると新しい物体になるので、`countIn` で、カードの ID を数える。
- **書いた 11 枚**（既存の IR と解釈器だけで書けた）: Rebuke、Gust、Retreat、Rune Prison、Solari Shieldbearer、First Mate、Pit Rookie、Grand Strategem、Unchecked Power、Flurry of Blades、Thermo Beam。テストは、肯定例と否定例（別の側や別の場所の物体は選べない、Might ちょうど 3 の境界、Buff で 4 になる、ルーンが exhausted で来る、など）。
- **エンジンの修正**: Might のフィルタは、Might を持たない物体（Battlefield など）に出会うと、フィルタ全体を「未理解」にして、対象を選べなくしていた。Might を持たない物体には当てはまらない（偽）に直した。また、Buff の +1 を数える。
- **レビューで見つかったこと**: Gust の Might が印刷の Might だけを見ていた（Buff を数えない）→ 直した。Equipment の加算と Passive は、まだ数えない（`ir-gaps.md`）。テストが誤った IR でも通る箇所があった → 否定例を足した。
- **書けなかった（今回の対象から外した）**: 複数の対象を選ぶ文（Kinkou Monk、Back to Back、Singularity）。Spell の選択は、1 つの対象ごとの選択だけを扱う。
- **次の単位**: 「〜してもよい」（`may`）。未転記の 45 枚に出る。選ぶ決定（はい／いいえ）を、決定フレームにする。

### ビューアのライブ操作に、「1 手戻す」を足した（2026-11-22）

- **おすすめの変更**: 予告は I12c でしたが、調べると、I12c は単独では成り立たない（`docs/termination.md` の 4b）。そこで、触っていて困る点（マリガンは、カードをクリックするとすぐ確定して、取り消せない）に向く、「1 手戻す」を先にした。
- **仕組み**: `riftbound-live` が、答え（`act`、`clock`、`judge`）の前のゲームを、積んで覚える。`undo` で、1 つ戻る。ゲームは、純粋な値なので、そのまま戻せる。**新しいゲーム、次のゲーム、サイドボードの入れ替えで、積みは空になる**（ゲームをまたいでは戻れない）。返事には、「何歩までを残すか」（`truncate`）と、合法手を入れる。橋渡しに `/api/undo`。
- **画面**: 「1 手戻す」のボタン（取り消せる答えがあるときだけ）と、Ctrl+Z（Cmd+Z）。ログと盤面を、その手までに切り詰める。
- **テスト**（`RiftboundTest/Live.lean`）: 戻したあとの返事が、同じ合法手と、残す歩数を言うこと、同じ答えを同じ局面に与えると、同じ返事になること（何も残らない）。期待を間違えると失敗することも確かめた。
- **まだ無いもの**: ゲームをまたぐ取り消し。やり直し（取り消しの取り消し）。

### I12a の実装の記録（2026-11-22）: Cleanup の停止

- **計画からの変更**: Cleanup が止まることを、`Invariant/Cleanup.lean` で証明した。撃破が必ず場の数を減らすには、撃破される Unit の持ち主がプレイヤーである必要がある。**これを不変条件として全部の腕で証明する代わりに（フレームのプレイヤーの妥当性まで通す必要があり、大きい）、`GameState.lethal` に「持ち主がプレイヤーである」を足した**。遊べるゲームでは動きは変わらない（既存のテストが通る）。そうでない物体は、遊べるゲームには存在しない。**定理には、`WF` のほかの前提が無い**。
- **証明したこと**: `cleanup_terminates`、`cleanup_no_infinite_run`。測度は 6 つの数の字引き順（場の物体の数、Board の外のトークンの数、離れた Equipment の数、Control を失った Battlefield の数、古い Contested の数、新しい Contested の数）。6 つの歩みのどれもが、測度を真に減らす。公理は標準の 3 つ。
- **作り方**: 数えるのは `List.countP` と `flatMap` の長さ。ゾーンから 1 枚抜くと全体の長さがちょうど 1 減る一般の補題（`length_flatMap_erase_one`）と、1 つの物体を変えても種類・位置・持ち主・Control を変えない `modObj` の補題で、歩みを 1 つずつ通した。
- **次の候補**: I12b（`run` の停止）、I12c、I12d。持ち主の妥当性を不変条件として証明すること（`lethal` の条件を外せる）。

### I12 の調査の記録（2026-11-22）: 自動処理の停止

- **証明はしていない**。何が要るかを調べ、`docs/termination.md` にまとめた。今ある確認は、テストと実測だけ。
- **実測**: 乱数の種 60 個 × 方針 4 通りの 240 ゲーム、答え 19,567 個で、1 つの答えのあとの作業フレームは最大 19 歩（平均 2.94）。fuel は 100。
- **テスト**（`RiftboundTest/Fuel.lean`）: デモのゲームを終わりまで遊び、fuel 切れとエンジンの内部エラーが出ないこと（Core Rules 12 種、時計つき 12 種、Limited 6 種）。期待を間違えると失敗することも確かめた。
- **見つけたこと**: 誘発した能力は、Chain に置かれたあと、決定フレーム（`chainPass`）を通らないと解決しないので、「誘発 → 解決 → また誘発」は 1 つの答えの中で続かない（コードを読んだ範囲）。止まらない恐れがあるのは、**`cleanup` の繰り返し**（撃破の `moveObj` が失敗すると、状態が変わらず永久に繰り返す。`WF` と `OwnerOk` の下では起きない）と、**`repeatN` と `forEach` を含む `run`**。
- **単位**: I12a（Cleanup の測度）、I12b（`run` の多重集合の測度）、I12c（残りと全体）、I12d（まとめ）。どれも大きい。

### M5b の実装の記録（2026-11-22）: I14 の全体（時間切れの後のターン数は有限）

- **計画からの変更なし**: 局所の事実（`Invariant/Clock.lean`）に足りなかった「ほかのどの腕も、ターンと時計を変えない」を、`Invariant/ClockRun.lean` で証明した。
- **証明したこと**: `Reachable.clockOk`（遊べるどのゲームでも、時計が決まっているなら、ターンの数は時計が名指したターンを超えない）、`step_keep`（1 手の後も同じで、**決まった時計は動かない**。時間切れを知らせられるのは一度だけだから: `legal_timeCalled`）、`Steps` と `time_called_bound`（**時間切れをターン `t` に知らせたら、その後のどの状態でも、ターンは `t + 3` を超えない**）。`beginTurn_ends` と合わせて、ゲームは有限のターン数で終わる。公理は標準の 3 つだけ。
- **作り方**: ターンと時計を書くのは、時間切れの知らせと、次のターンの始まり（`beginTurnStep`）の 2 か所だけ（`Frames.lean`）。`applyFrame0` の腕（`applyFrame0_tc`: 変えないか、時間切れを知らせる）と `microStep0` の腕（`microStep0_tick`: 変えないか、時計が尽きていないときに次のターンへ）を、ほかの不変条件と同じように、既存の `SameMeta`・`Safe`・`SafeP` の補題で 1 腕ずつ通した。出発点は、`addCards` から `addLimitedDecks` までを `wf` の補題と同じ形で通した（時計は `none`）。
- **まだ無いもの**: ゲームの合間に時間切れになったときの扱い（TR 408.2.d）、シングルエリミネーション（TR 408.4）、2v2 の時間切れ。「有限」は、ターン数の上限（`t + 3`）で述べた。1 ターンの中の手数の上限は、I12（自動処理の停止）の話で、この証明の外。
- **次の候補**: `GameConfig.Valid`（TR の原文が要る）、Limited のデッキでマッチ、カードを直接クリックして答える操作。

### ビューアのライブ操作に、サイドボードの入れ替えを足した（2026-11-22）

- **何ができるか**: 大会の Constructed の Best of 1 / 3 で、ゲームが終わってマッチが続くとき、**サイドボードを使えるなら、画面で、Main Deck のカードを 1 枚出し、サイドボードのカードを 1 枚入れる**。入れ替えの後のデッキが、Constructed で合法かどうかは、Lean が確かめる（`ConstructedDeckValid`）。合法なら、次のゲームが、そのデッキで始まる。サイドボードを使えない（最初のゲームの前、引き分けの後）ときは、画面に出ない（TR 403.5、403.10）。
- **Lean 側**（`RiftboundDriver/Live.lean`）: `LiveGame` に、プレイヤーのデッキとサイドボード（`decks`、`sides`）を持たせ、`liveNew` と `liveNext` が、そのデッキでゲームを作る。`liveSwap`: マッチが許し（`sideboardAllowed`）、ゲームが終わっていて、出すカードが Main Deck に、入れるカードがサイドボードにあり、入れ替えの後のデッキが合法のときだけ受ける。そうでなければ、理由つきで拒否する。返事に、サイドボードの状態（Main Deck とサイドボードのカードと枚数、使えるか）を入れた。入れ替える人は、操作する席の最初のプレイヤー（もう一方のデッキは変わらない）。
- **デモのデッキ**: デモのカードを、デモの組（`demoSet`）に属させ、`demoEnv` でそれを合法にした。デモのデッキは、**合法な Constructed のデッキ**で、10 枚のサイドボード（Quick Study ×3、Scout ×3、Banner ×3、Vanilla 0 ×1）を持つ（`demoSideboard`）。
- **証明との関係**: 画面の入れ替えは、1 対 1 で、`IsSwap`（`Tournament/Sideboard.lean`）の形になる。証明した `constructedValid_swap` は、合法なデッキの入れ替えの後、確かめることは Chosen Champion・種類・Signature・Domain Identity の 4 つだけ、と言う。**画面の確認は、`ConstructedDeckValid` を直接計算する**（`constructedValid_swap` を画面が使うわけではない。両者が食い違わないことは、テストで確かめた）。
- **橋渡し**: `/api/swap`（カードの id は、英数字・`_`・`-` の 24 文字までに限る）。
- **テスト**（`RiftboundTest/Live.lean`）: Spark を Quick Study に入れ替えると、Main Deck は 40 枚のまま、サイドボードは 10 枚のまま、デッキは合法で、次のゲームの P0 のカードは Quick Study 1 枚・Spark 2 枚になること、無いカードと、Chosen Champion を入れ替えられないカードで替えること（TR 403.4.c）と、終わっていないゲームでは拒否されること、引き分けの後、Best of 1 が終わった後、Constructed でない試合では拒否されること。期待を間違えると失敗することも確かめた。
- **実ブラウザで確かめたこと**: Best of 3 で、P0 が投了したあと、サイドボードの欄が出る。Hero を Quick Study に替えるのは「the deck would not be a legal Constructed deck」と拒否される。Spark を Quick Study に替えると、枚数が更新され、「次のゲーム」で先手を選ぶと、そのゲームの P0 の札は Quick Study 1 枚・Spark 2 枚。
- **まだ無いもの**: 2 つ以上の入れ替えを、途中の合法性を無視してまとめて行うこと（今は、1 枚ずつ、毎回、合法でなければ拒否する）、Chosen Champion を別の Champion に替えること（デモに 2 枚目の Champion が無い）、2 人とも人のときの両方のデッキ、Limited のサイドボード（TR 602.4.a.7）、次のマッチの前に、登録した状態へ戻すこと（TR 403.8: 新しいゲームを始めると、登録したデッキに戻る）。
- **次の候補**: I14 の全体、TR の原文を置いてもらうこと（`GameConfig.Valid` など）、カードを直接クリックして答える操作、2 人とも人のときの隠れ情報（M9）。

### ビューアのライブ操作で、設定（ルール・時計・ジャッジ・マッチ）を選べるようにした（2026-11-22）

- **何ができるか**: ライブ操作の画面で、ルール（Core Rules・大会の Constructed・Sealed・Draft）と、試合（1 ゲームだけ・Best of 1・Best of 3）を選べる。大会のルールでは、「時計: 時間切れを知らせる」と「ジャッジ: 引き分けを宣言する」のボタンが、**合法なときだけ**出る（合法かどうかは、Lean の `Legal` が決める）。M5b で作った層（時計・ジャッジ・マッチ・先手・サイドボードの可否・Limited）を、画面で動かして確かめられる。
- **Lean 側**（`RiftboundDriver/Live.lean`）: `LiveKind`（core・constructed・sealed・draft）、`LiveGame` にマッチ（`MatchState`）と、先手を決める順（`order`）を足した。`settle`（ゲームが終わったら、結果をマッチへ一度だけ数える）、`liveExternal`（時計とジャッジの答え。選手の答えではない）、`liveNext`（マッチの次のゲーム: **先手か後手かを選ぶのが、操作する席のプレイヤーなら、選ぶまで待つ**。自動の席なら先手を選ぶ。引き分けの後は同じ順: TR 407）。返事に、マッチの状態（勝ち数・ゲーム数・次の順・サイドボードの可否・同じ Battlefield）と、時計とジャッジが今できるかを入れた。ゲームの seed は、マッチの seed に、終えたゲームの数を足したもの。
- **橋渡し**: `/api/clock`、`/api/judge`、`/api/next`（選択は `first` か `second`）を足した。値は許すものだけを受ける。
- **テスト**（`RiftboundTest/Live.lean`）: 時計とジャッジは、大会のルールで効き、Core Rules では拒否される、Sealed のゲームは Legend が無い、Best of 1 は 1 ゲームで終わり、次のゲームが無い、Best of 3 は続き、負けた人が選ぶ（先手を選ぶとその人が先手、後手を選ぶともう一方が先手）、マッチでないゲームと、終わっていないゲームには、次のゲームが無い。期待を間違えると失敗することも確かめた。
- **実ブラウザで確かめたこと**: Best of 3 の Constructed で、時計のボタン→ゲーム 1 が引き分け→マッチは「次の先手は同じ P0」「サイドボード: 使えない」「同じ Battlefield」→次のゲーム→投了→勝ち P0 0 - P1 1、「負けた P0 が選ぶ」、「サイドボード: 使える」→「次のゲーム」で先手か後手かを問われ、「後手にする」を押すと、次のゲームの最初のターンは P1。
- **まだ無いもの**: サイドボードの入れ替えの画面（「使える」と表示するだけ）、2 人とも人のときの隠れ情報、カードを直接クリックする操作、マッチの途中でデッキを変えること。
- **次の候補**: サイドボードの入れ替えの画面（`IsSwap` と `constructedValid_swap` を画面で使う）、I14 の全体、TR の原文を置いてもらうこと。

### ビューアのライブ操作の実装の記録（2026-11-22、Issue #14）

- **何ができるか**: 画面のボタンで、`legalActions` の合法手から答えを選んで、ゲームを進められる。ルールは Lean だけにあり、画面も橋渡しも持たない（境界は、Issue #14 の注意のとおり）。詳細は [viewer.md](viewer.md)。
- **決めたこと（Issue の 4 つの問い）**: ①通信は、Lean の実行ファイル（`riftbound-live`）を標準入出力で子プロセスにし、Python の薄い橋渡し（`scripts/live.py`）が localhost の HTTP にする。Lean 側は JSON を読まず、「`start SEED 席`」「`act 番号`」の 1 行だけを読む。②状態は、手ごとに、トレースと同じ形で丸ごと送る。③`Event` に Rune Pool と Exhaust の変化は足さない。④操作する席は、画面で選ぶ（P0 だけ、P1 だけ、両方）。操作しない席と乱数の質問は `demoAnswer`。
- **Lean 側**（`RiftboundDriver/Live.lean`）: `LiveGame`（状態、画面が知っているオブジェクト、手の番号、乱数、操作する席）、`legal`（操作する席の合法手と、投了）、`needsHuman`、`apply`（`step` を 1 回）、`autoRun`（人の質問まで、自動で答える）、`liveStart`、`liveAct`。答えは、直前の合法手の一覧の番号で送る。範囲外の番号は拒否する。アクションの JSON に、払った Power の内訳（`power`）を足した（同じカードの、払い方の違うボタンを区別するため）。
- **橋渡しの安全**: `127.0.0.1` だけで待ち受け、Host と Origin を確かめ、POST は JSON だけを受ける。実際に、別の Host・別の Origin・テキストの POST は拒否されることを確かめた。
- **画面**: ライブ操作の欄は、橋渡しが見つかったときだけ出る（Artifact のページや `file://` では、再生だけ）。ボタンは、最新の手のときだけ出て、ログの前の手を見ているときは隠れる。押すと、返ってきた手（自動の答えも含む）がアニメーションで再生される。`describe` を `describeA(答え, 開いていた質問)` に分け、ボタンの文に使う。マリガンと捨てるボタンに、カード名を入れた。
- **テスト**（`RiftboundTest/Live.lean`）: 人の質問で止まり、人の席の合法手だけを出すこと、範囲外の番号を拒否すること、マリガンを終えると次の質問まで進むこと、両方の席を操作すると、投了が 2 つ出ること、投了でゲームが終わり、その後は何も出ないこと。期待を間違えると失敗することも確かめた。**実ブラウザで、44 回ボタンを押してターン 8 まで進めた**（エラー無し）。両席の操作と投了（勝者の表示）も確かめた。
- **直した不具合（使ってもらって見つかった）**: 橋渡しが無い環境（Artifact のページ）で、ライブ操作の欄が見え、「新しいゲーム」を押すと JSON のエラーが出た。原因は、`.live { display: grid }` が `hidden` 属性を上書きしていたこと。`[hidden] { display: none !important }` を足し、橋渡しの応答が JSON でないときは、「橋渡し（scripts/live.py）につながっていない」と出すようにした。橋渡しが無い環境と、ある環境の両方を、実ブラウザで確かめた。
- **まだ無いもの**: 時計・ジャッジ・Limited の設定の選択（今はデモのデッキを Core Rules で動かす）、2 人とも人のときの隠れ情報（相手の手札が見える）、カードを直接クリックして答える操作（今は文のボタン）、複数のゲームを同時に持つこと。
- **次の候補**: ライブ操作で、設定（時計・ジャッジ・Limited・マッチ）を選べるようにする、I14 の全体、Limited のデッキでマッチ、TR の原文を置いてもらうこと（`GameConfig.Valid` など）。

### M5b の実装の記録（2026-11-22）: Limited のデッキからゲームを始める（TR 602.4）

- **入れたもの**: `GameState.initialLimited db env config decks`（`Rules/Setup.lean`）。Sealed か Draft の設定で、`LimitedDeck`（Legend と Chosen Champion は無くてよい）から、ゲームの最初の状態を作る。Legend や Chosen Champion が無いデッキは、そのゾーンが空になる。追加ドロー（前の単位）は、そのゾーンを読むので、**実際のデッキで動く**。
- **始められる条件**（`LimitedStartOk`）: デッキの数がプレイヤーの数と同じ、設定が遊べる（`GameConfig.Valid`）、Limited のフォーマット（`RuleSet.limitedMinMain` が値を持つ）、どのデッキも `LimitedDeckValid`（Sealed は 25 枚以上、Draft は 20 枚以上: TR 602.4）、**どのデッキも Battlefield を 1 枚以上持つ**（無作為な選択のため: CR 487.5。Limited の Battlefield の枚数は TR 602.3 の原文が要るので、1 枚以上だけを求めた）。Core Rules と Constructed では `none`。
- **証明**: 既存の `addDeck` の補題（`addDeck_wf`、`_ownerOk`、`_grows`、`_hand`）と、その `addDecks` 版を、`addLimitedDeck` 用に複製して通した。`initialLimited_wf`・`_ownerOk`・`_setup`・`_pending`・`_setupInv`・`_stack`・`_handInv`、`LimitedStartOk.battlefields`。**`Reachable` の出発点を `Start`（Core のゲームか Limited のゲーム）にした**ので、`Reachable.inv`・`setup`・`stack`・`handInv` が Limited のゲームにも成り立つ（`Reachable.progress` などは、これらから従う）。
- **テスト**（`RiftboundTest/LimitedStart.lean`）: Sealed の 25 枚で始まる（Legend も Chosen Champion も無くてよい）、24 枚では始まらない、Draft は 20 枚、Constructed と Core Rules では始まらない、Battlefield が無い・Rune が 11 枚・Domain Identity の外のカードがあると始まらない、デッキが 1 つでは始まらない、Legend と Chosen Champion のゾーンが空（あるデッキは 1 枚）、追加ドローの手札（Legend だけ無い、Chosen Champion だけ無い、両方無い、ある）。期待を間違えると失敗することも確かめた。
- **ビューア**: `riftbound-trace seed turns limited` が、`initialLimited` で、Legend も Chosen Champion も無い Sealed のデッキ（`demoLimitedDeck`）のゲームを出す。seed 2 では、Legend と Champion のゾーンが空で、ターン 1 の P1 の手札が 6 枚（通常は 5 枚）。
- **まだ無いもの（M5b の残り）**: Limited の Battlefield（blank、1 マッチに 1 回: TR 602.3）、Limited の Domain Identity の「1 ドメイン + Legend のドメイン」（TR 602.4.a.3）、Limited のデッキの Rune Deck の枚数と領域（TR の原文が要る）、I14 の全体、ゲームの合間の時間切れ、シングルエリミネーション、2v2、`GameConfig.Valid`、Bo1 の準備、TR 403.8。
- **次の候補**: Limited のデッキでマッチを行う（`riftbound-match` が Limited の設定を受ける）、I14 の全体、ビューアのライブ操作（Issue #14）。

### M5b の実装の記録（2026-11-22）: Limited の追加ドロー（TR 602.4.a.5.b）

- **フォーマットが、ゲームの進行を変える最初の例**: エンジンが `GameConfig.ruleSet`（フォーマット）と、プレイヤーの Legend・Chosen Champion のゾーンを読んで動く。Limited（Sealed と Draft）で、Legend か Chosen Champion を使わないデッキのプレイヤーは、**自分の最初の Beginning Phase の始まりに、1 枚引く**。両方なくても 1 枚。
- **実装**: `GameState.extraDraws s p`（0 か 1）。Limited で、最初の 1 周（`turn ≤ プレイヤー数`）で、Legend のゾーンか Chosen Champion のゾーンが空なら 1。`phase .beginning` の腕が、`.draw p (extraDraws)` のフレームを `cleanup` の前に積む（`.draw p 0` は何もせず消える）。`Format.isLimited`、`RuleSet.isLimited`。
- **証明**（`Invariant/LimitedDraw.lean`）: `extraDraws_zero_of_not_limited`（Core Rules と Constructed では引かない）、`extraDraws_le_one`（多くて 1 枚: 両方なくても 1 枚）、`extraDraws_eq_one_iff`（Limited で、最初の 1 周で、どちらかのゾーンが空、のとき、かつそのときだけ 1）、`extraDraws_zero_late`（最初の 1 周より後は 0）。不変条件は、`phase .beginning` の腕の、Setup の 1 か所だけ直した（積むフレームの一覧に `draw` を足した）。
- **読み方の決定（要確認）**: 規則の文は「各ゲームの最初の Beginning Phase」。**「自分の最初の Beginning Phase」と読み、両方のプレイヤーが 1 回ずつ引く**ようにした。「ゲームの最初の Beginning Phase だけ（先手だけ）」とも読めるが、TR の原文がリポジトリに無く、確かめられない（[tournament-model.md §7](tournament-model.md#7-曖昧な点と要確認事項)）。
- **テスト**（`RiftboundTest/LimitedDraw.lean`）: Sealed で Legend が無いと 1 枚多いこと、Chosen Champion が無くても同じこと、両方なくても 1 枚だけのこと、後手は 2 ターン目に引き、先手は 3 ターン目に重ねて引かないこと、Constructed と Core Rules では引かないこと。期待を間違えると失敗することも確かめた。
- **ビューア**: `riftbound-trace seed turns limited` が、Sealed で Legend の無いデッキのゲームを出す。seed 2 では、ターン 1 の P1 の手札が 5 枚から 6 枚（Main Phase の始まり）、ターン 2 の P0 の手札が 5 枚から 6 枚になり、通常のゲームより 1 枚多い。
- **まだ無いもの（M5b の残り）**: **Limited のデッキ（`LimitedDeck`）からゲームを始めること**（`GameState.initial` は、Legend と Chosen Champion のあるデッキだけを受け付ける。今回のテストは、ゾーンを空にして代用した）、Limited の Battlefield（blank、1 マッチに 1 回: TR 602.3）、I14 の全体、ゲームの合間の時間切れ（TR 408.2.d）、シングルエリミネーション、2v2、`GameConfig.Valid`、Bo1 の準備、TR 403.8。
- **次の候補**: `LimitedDeck` からゲームを始める（今回の追加ドローが、実際のデッキで動く）、I14 の全体、ビューアのライブ操作（Issue #14）。

### M5b の実装の記録（2026-11-22）: 先手の決め方をゲームにつなぐ（TR 407）

- **着手前に確かめたこと**: エンジンは、ターン順を、質問 `chanceTurnOrder` への答え（外から来る: CR 115）で受け取る。**どの並びも合法**なので、エンジンを変える必要は無かった。足りなかったのは、マッチの層の「誰が先手を選ぶか」から、その答えを作る部分と、両者をつなぐ事実だった。
- **マッチ側**（`Tournament/Match.lean`）: `Order.chooser`（選ぶ人: 最初のゲームは抽選で選ばれた人、勝負がついた後は負けた人、引き分けの後は選ばない）、`Order.first`（選ぶ人が先手か後手かを選ぶ。引き分けの後は同じ順）、`turnOrderOf`（先手を決めたターン順）。定理: `Order.first_same`（引き分けの後は同じ人が先手: TR 407.4）、`first_loser`（負けた人が選ぶ）、`first_chance`（最初のゲーム: TR 407.1、407.2）、`first_lt`・`other_lt`（先手はマッチの 2 人のどちらか）、`turnOrderOf_perm`（2 人の並びである）。
- **つなぐ事実**（`Tournament/FirstPlayer.lean`）: `turnOrder_answer_legal`（選んだ先手のターン順は、`chanceTurnOrder` への合法な答え）、`turnOrder_answer_sets`（その答えがゲームのターン順になる）、`first_turns`（最初のターンは選ばれた人、2 番目のターンはもう一人）。
- **モデルの決定**: 答えは、選ぶ人ではなく、**「乱数」の行為者**が出す（今までと同じ）。**選ぶ人の選択は、エンジンの外（マッチ）で行い、答えとして届く**。選ぶ人の決定を、エンジンの中のフレームにする（選ぶ人の行為者で、先手か後手かを答える）ことはしていない。
- **ドライバー**: `riftbound-match` が、マッチの `nextOrder` から先手を決め、`chanceTurnOrder` へ答える。**選ぶ人は先手を選ぶ**という方針を置いた（デモ用）。抽選は、seed の偶奇。ログに、誰が選んだか（抽選の人・負けた人・引き分けの後は同じ順）と先手を出す。seed 4 では、引き分けの次のゲームで、同じ人が先手になる。
- **テスト**（`RiftboundTest/FirstPlayer.lean`）: `Order.first` の場合分け、ターン順の答えの後に、選ばれた人が最初のターンを行うこと（両方の向き）、並びになっていない答えと、選手が出した答えは拒否されること。期待を間違えると失敗することも確かめた。
- **まだ無いもの（M5b の残り）**: 選ぶ人の決定をエンジンの中に持つこと、I14 の全体、ゲームの合間の時間切れ（TR 408.2.d）、シングルエリミネーション、2v2（TR 603.7: チームの手番順）、`GameConfig.Valid`、Bo1 の準備（TR 406.1.h）、Limited の追加ドロー、TR 403.8。
- **次の候補**: Limited の追加ドロー（TR 602.4.a.5.b）、I14 の全体、ビューアのライブ操作（Issue #14）。

### M5b の実装の記録（2026-11-22）: サイドボードの入れ替え（TR 403）

- **入れたもの**（`Tournament/Sideboard.lean`）: サイドボードの入れ替え `IsSwap main side main' side'`（Main Deck から何枚かが出て、同じ枚数がサイドボードから入り、出たカードがサイドボードへ行く: TR 403.4）。カードは多重集合として扱う（`List.Perm`）。`SideboardStep`（マッチが許し、かつ入れ替えであること）。
- **証明**: `IsSwap.pool`（Main Deck とサイドボードを合わせたカードは変わらない）、`IsSwap.main_length`・`side_length`（Main Deck もサイドボードも、枚数が変わらない: 1 対 1）、`copyLimitOk_perm`（同名の枚数制限は、順番に依らない）、**`Resolved.constructedValid_swap`**: 合法な Constructed のデッキと入れ替えから、新しいデッキが合法であるために確かめることは、**Chosen Champion（変えてよい: TR 403.4.a）、種類、Signature、Domain Identity の 4 つだけ**。Main Deck の 40 枚、サイドボードの 10 枚以下、同名の枚数制限（Main Deck とサイドボードの合計: TR 601.1.c）、各カードの合法性は、確かめなくてよい。Legend・Rune・Battlefield は、入れ替えの対象外で変わらない（TR 403.4.b）。`not_sideboardStep_start`・`not_sideboardStep_draw`（最初のゲームの前と、引き分けの後は入れ替えられない: TR 403.5、403.10）。
- **テスト**（`RiftboundTest/Sideboard.lean`）: 1 対 1 の入れ替えの後も合法であること、合計の枚数が同じこと、1 対 1 でない入れ替えは Main Deck の 40 枚が崩れること、同名の枚数制限が Main Deck とサイドボードの合計であること、マッチが許す場合。期待を間違えると失敗することも確かめた。
- **`GameConfig.Valid` は入れていない**: モードとフォーマットの組のうち、TR が手続きを定めているものを決めるには、TR の 600 番台の原文が要るが、リポジトリに無い（[tournament-model.md §7](tournament-model.md#7-曖昧な点と要確認事項) の 6 番）。推測で入れない。
- **まだ無いもの（M5b の残り）**: I14 の全体、ゲームの合間の時間切れ（TR 408.2.d）、シングルエリミネーション（TR 408.4）、2v2、選手が自分で合意を申し出る手順、`GameConfig.Valid`、Bo1 の準備（TR 406.1.h）、Limited の追加ドロー（TR 602.4.a.5.b）、エンジンが先手の選択を受け取ること、TR 403.8（次のマッチの前に登録した状態へ戻す）。
- **次の候補**: Limited の追加ドロー（TR 602.4.a.5.b）、エンジンが先手の選択を受け取ること、I14 の全体。

### M5b の実装の記録（2026-11-22）: ジャッジの引き分け（合意と終わらないループ）

- **計画どおり**: 時計と同じ形で入れた。`ActionKind.declareDraw`（行為者は「ジャッジ」）。合法なのは、Tournament Rules の設定で、どの質問が開いていても（ゲームの準備の途中でも）。選手や時計が送っても、Core Rules だけの設定でも、不合法。`legalActions` には出ない。
- **意味**: ゲームを、その場で引き分けで終える（`result := some .draw`、スタックは空）。点差は見ない（1-3 でも引き分け）。選手の合意（TR 410.1）も、終わらないループ（TR 505.6）も、**エンジンの外の判断**で、ジャッジが宣言する。エンジンはループを見つけない（[tournament-model.md §5](tournament-model.md#5-ループtr-505)）。**2 つの理由は区別していない**（どちらも同じ結果になる）。
- **証明**（`Invariant/Draw.lean`）: `applyFrame0_declareDraw`、`declareDraw_draws`（結果は引き分けで、フレームは残らない）、`legal_declareDraw`（合法な宣言はジャッジの行為で、Tournament の設定）、`not_legal_of_result`（ゲームが終わったら、何も合法でない: 引き分けの後も）。投了（`concede`）と違い、枠の中の答えにしたので、不変条件の腕は 7 つの `applyFrame0` の補題に 1 つずつ足すだけで済んだ。
- **マッチ側**（TR 410.2）: `MatchState.concedeMatch`（マッチを投了すると、もう一方が勝つ）、`concedeMatch_ne`（勝者は投了した人ではない）、`agreedDrawMatch`（合意の引き分け）。**マッチの 2 人は、プレイヤー 0 と 1 に限る**。
- **ビューア・ドライバー**: `riftbound-trace seed turns judge` が、`turns` ターンの後にジャッジが引き分けを宣言するトレースを出す。ビューアは「ジャッジ: 引き分けを宣言する」と、結果の「引き分け」を表示する。
- **テスト**（`RiftboundTest/Judge.lean`）: ジャッジの宣言でゲームが終わり（3 点リードしていても）、その後は何も合法でないこと、選手と時計の宣言は不合法で、Core Rules にはジャッジがないこと、ゲームの準備の途中でも宣言できること、マッチの投了と合意の引き分け。期待を間違えると失敗することも確かめた。
- **まだ無いもの（M5b の残り）**: I14 の全体、ゲームの合間に時間切れになったときの扱い（TR 408.2.d）、シングルエリミネーション（TR 408.4）、2v2、ゲーム単位の投了と合意の引き分けで、**選手が自分で合意を申し出る手順**（今は、ジャッジが宣言する）、`GameConfig.Valid`、サイドボード後のデッキの合法性（TR 403.4.c）、Bo1 の準備（TR 406.1.h）、Limited の追加ドロー、エンジンが先手の選択を受け取ること。
- **次の候補**: サイドボード後のデッキの合法性（TR 403.4.c）、`GameConfig.Valid`、I14 の全体。

### M5b の実装の記録（2026-11-22）: 時計（時間切れ）

- **計画からの変更なし、ただし証明は局所版**: 時計の `Action` と追加 3 ターンをエンジンの中に入れた。**I14 の全体（どんな実行でも、時間切れの後のターン数は有限）は、まだ証明していない**。局所の事実（下）だけ証明した。全体には、「ほかのどの腕も、ターンと時計を変えない」という補題が要る。
- **時計**（`GameState.clock : Option Nat`）: 時間切れを知らせた時点のターン `t` に対して、`t + 3` を持つ。時間切れを知らせるのは、行為者を「時計」とする `Action`（`ActionKind.timeCalled`）。合法なのは、Tournament Rules の設定で、1v1 で、最初のターンが始まった後で、まだ知らせていないとき（`LegalFrame`、TR 408.2）。行為者が選手やジャッジなら不合法。`legalActions` には出ない（選手の答えではない）。Core Rules だけの設定には、時計が無い。
- **終わり方**（`beginTurnStep`）: ターンが始まるとき、時計が尽きていたら（`clockDue`: 時計が名指したターンが、もう始まった）、次のターンを始めずに、ゲームを終える。結果は `gameOnTime`（2 点以上リードした方が勝ち、そうでなければ引き分け: TR 408.2）。`t` のターンの途中で知らせれば、`t` のターンを最後まで行い、`t + 1`、`t + 2`、`t + 3` のターンを行って、終わる。
- **証明**（`Invariant/Clock.lean`）: `applyFrame0_timeCalled`、`timeCalled_sets_clock`（時計は `ターン + 3`、ほかは変わらない）、`legal_timeCalled`（合法な知らせは時計の行為・Tournament・1v1・一度だけ）、`clockDue_iff`、`three_more_turns`（`t + 1`、`t + 2`、`t + 3` では尽きず、`t + 3` の後で尽きる）、`beginTurn_ends`（尽きたらゲームが終わり、結果は点差で決まる）、`beginTurn_next`（尽きていなければ次のターンが始まり、名指されたターンを超えない）。
- **ほかの不変条件**: `microStep0` の `beginTurn` の腕は、`beginTurnStep_cases`（普通の始まりか、ゲームの終わりか）で場合分けした。7 つの不変条件（Frames の WF と物理カード、OwnerOk、手札、スタック、Setup）の `beginTurn` の腕と `timeCalled` の腕を足した。
- **ドライバー**（`playUntilEnd`）: 上限 `cap` に達したら、時計の `Action` を送る。**前の PR のターン数の上限という近似は、なくなった**。ゲームは `cap + 3` ターンで終わる。`riftbound-trace seed turns clock` は、時計を含むトレースを出す。ビューアは「時計: 時間切れを知らせる」を表示する。
- **テスト**（`RiftboundTest/Clock.lean`）: 時計だけが、Tournament の設定で、一度だけ知らせられること、Core Rules では知らせられないこと、ターン 2 で知らせると、ターン 5 が始まった後で終わって引き分けになること、2 点リードなら勝ち、1 点なら引き分けになること。期待を間違えると失敗することも確かめた。
- **まだ無いもの（M5b の残り）**: I14 の全体、ゲームの合間に時間切れになったときは新しいゲームを始めない（TR 408.2.d）、シングルエリミネーション（TR 408.4）、2v2 の時間切れ、ジャッジの引き分け（TR 505.6）、投了と合意の引き分け（TR 410）、`GameConfig.Valid`、サイドボード後のデッキの合法性（TR 403.4.c）、エンジンが先手の選択を受け取ること。
- **次の候補**: I14 の全体（ターンと時計が、ほかの腕で変わらないこと）、ジャッジの引き分けと投了・合意の引き分け（TR 410、505.6）、サイドボード後のデッキの合法性（TR 403.4.c）。

### M5b の実装の記録（2026-11-22）: マッチの層（最初の単位）

- **着手前に確かめたこと**: マッチと大会の層は、デッキの合法性（`Tournament/DeckLegality.lean`）と `Format` だけで、**`Match` は無かった**。M5b の計画のうち、ゲームの外の規則（数と結果だけの関数）を先に入れた。エンジンの中の規則（時計の `Action`、追加 3 ターン、ジャッジの引き分け、投了と合意の引き分け）は、次の単位に残る。
- **`MatchState`**（`Tournament/Match.lean`）: 勝つのに要る数（Bo1 は 1、Bo3 は 2: TR 404.1）、各自の勝ち数、ゲーム数、前のゲームの結果と先手。`record` が、1 ゲームの結果を足す。**引き分けは、勝ち数に数えず、ゲームだけ数える**（TR 404.3）。終わったマッチは変わらない。
- **規則を関数にした**: `sideboardAllowed`（最初のゲームの前は不可: TR 403.5、引き分けの後は不可: TR 403.10）、`reuseBattlefields`（引き分けの後は同じ Battlefield: TR 406.1.b）、`nextOrder`（最初はランダムな人が選ぶ: TR 407.1、勝負がついた後は負けた人が選ぶ、引き分けの後は同じ順: TR 407.4）、`onTime`（時間切れのマッチ: 勝ち数の多い方が勝ち、同数は引き分け: TR 404.4-404.5、408.3）、`gameOnTime`（時間切れのゲーム: 2 点以上リードした方が勝ち、そうでなければ引き分け: TR 408.2）。
- **証明**: `record_draw_wins`（引き分けは勝ち数を変えない）、`record_finished`（終わったマッチは変わらない）、`MatchState.Inv`（目標が正で、両方が目標に届かず、勝ち数は試合数以下）と、`start_inv`、`record_inv`、`ofGames_inv`（どんな結果の列でも保たれる）、`Inv.winner_unique`（勝者は高々 1 人。TR 404.1）、`Inv.winner_spec`、`sideboard_not_first`、`sideboard_not_after_draw`、`after_draw`、`after_win`、`onTime_won`、`onTime_draw_iff`、`gameOnTime_draw_iff`、`gameOnTime_won`。
- **ドライバー**（`RiftboundDriver/Match.lean`、`riftbound-match`）: デモのゲームを 1 つずつ行い、結果を `MatchState.record` に渡す。**時計の代わりに、ターン数の上限 `cap`**を置き、上限に達したら、`gameOnTime` で点差から結果を決める。TR 408.2 の「現在のターンを終え、さらに 3 ターン」は、まだ入れていない（エンジンの中の規則なので、次の単位）。
- **テスト**（`RiftboundTest/Match.lean`）: 引き分けを数えないこと、勝ち数 2 で終わること、終わったマッチは変わらないこと、サイドボードの可否、次のゲームの決め方、時間切れ。期待を間違えると失敗することも確かめた。
- **まだ無いもの（M5b の残り）**: `GameConfig.Valid`、時計の `Action` と追加 3 ターン（I14）、ジャッジによるループの引き分け（TR 505.6）、投了と合意の引き分け（TR 410）、Bo1 の準備手順（TR 406.1.h）、シングルエリミネーションの手順（TR 408.4）、Limited の追加ドロー（TR 602.4.a.5.b）、サイドボードの入れ替えの後もデッキが合法であること（TR 403.4.c）、**エンジンが「先手は選んだ人」を受け取ること**（今は、ゲームの先手は、エンジンが偶然の決定で決める）。
- **次の候補**: 時計の `Action` と追加 3 ターン（I14）、サイドボードの入れ替えの後も合法であること（TR 403.4.c）、`GameConfig.Valid`。

### M7k の実装の記録（2026-11-22）: Legion と「追加コストを払ったなら」、書ける文の数え直し

- **数え直した結果（計画の見直し）**: 前の報告のおすすめは、Hidden・Empower・Flow から選ぶことだった。転記済み（`.meta` があり、効果が未転記）のカード 900 枚を数えると、**これらのキーワードは、書ける枚数が少ない**。効果まで書けているカードは、Hidden が 44 枚中 3 枚、Empower が 40 枚中 1 枚、Flow が 15 枚中 3 枚。さらに、Hidden を持つ未転記の 40 枚は、ほかの文も書けないので、Hidden を入れても 1 枚も増えない。
- **未転記 900 枚の詰まり方**: 書けない文の種類は、1 枚に 1 種類（747 枚）か 2 種類（142 枚）。ただし**種類の多くは、そのカードにしか出ない文**で、1 つの種類を直して増えるカードは、多くて 2 枚。貪欲に 15 種類を直しても、増えるのは 23 枚。**書ける枚数を増やす 1 回の PR の収穫は、これから先、10 枚前後になる**。
- **選んだもの**: 数えて、まとまって書ける 2 種類を入れた。Legion の誘発（4 枚: OGN-016、020、217、218）と、追加コストを払ったときの誘発（4 枚: SFD-013、SFD-067、SFD-098、VEN-120）。**転記済みは 202 枚から 210 枚になった**。
- **play したときの事実**（`Object.paid`、`legion`、`playedTurn`、`PlayMark`、`GameState.playedBefore`）: カードを play するとき、追加コストを払ったか、同じ番に自分が別のカードを play していたか、その番を、object に残す。`applyCast` と `applyPlay` が `Object.withPlay` で書く。番の記録は、object の移動で残るので、1 つの番の中で、play されたカードが墓地へ行っても数えられる。
- **誘発の条件**（`condOk`）: 誘発の条件に、`Condition.paid` と `Condition.legion` を入れた。規則どおり、「When X, if Y」の条件は、誘発するとき（Chain に載せる前）に確かめる。条件が偽なら、対象も選ばない。`Condition.eval` も、効果の中の条件として、同じ値を返す。
- **追加コストの文**（`CardDef.additionalCost`）: 「You may pay ... as an additional cost to play me」を、カードの欄にした。`extraCosts` が、キーワードの追加コストと並べて数える（同時に 2 つは払えない）。
- **転記**（`scripts/transcribe.py`）: `[Legion] — When you play me, ...`、`When you play me, if you paid the additional cost, ...`、追加コストの行。**追加コストが Energy と Power のものだけ**。kill・discard・exhaust の追加コストは、費用の種類が足りないので、書かなかった。
- **テスト**: `RiftboundTest/Optional.lean` に、Legion（単独では引かず、別のカードの後なら引く）と、追加コスト（払わなければ引かず、払えば引く）。期待を間違えると失敗することも確かめた。
- **ビューア・デモ**: デモの Archer は Legion（別のカードを play した後だけ、1 ダメージ）、Looter は追加コスト 1 Energy を払ったときだけ、捨てて引く。seed 5 の 18 番で Archer の誘発が起き（対象を選ぶ）、119 番では起きない。72 番で Looter が払って引く。
- **まだ無いもの**: 追加コストが kill・discard・exhaust・XP のカード（13 枚中の 6 枚）、「ready me and give me +N this turn」などの文（Pyke）、Legion の費用軽減（「I cost less」）、Hidden・Empower・Flow。
- **次の候補**: 書ける枚数の増加は頭打ちに近い。**マッチと大会の手続き（M5b）、ビューアのライブ操作（Issue #14）、不変条件の拡張**。

### M7j の実装の記録（2026-11-22）: Accelerate と Repeat（払うかどうかを選ぶ追加コスト）

- **数え直した結果**: 転記済みで Accelerate を持つ Unit は 31 枚、Repeat を持つ Spell は 20 枚。ただし Repeat のうち、**効果まで書けているのは 5 枚**（SFD-031、SFD-034、SFD-066、UNL-009、UNL-061）で、残り 15 枚は効果が未転記なので、Repeat が動いても見えない。前の報告の 32 枚と 24 枚は、データの文の数で、動くカードの数ではなかった。
- **計画からの変更**: 前の報告では「行動に選択の項を足す」としたが、**払う額で選ぶ形にした**。行動の型（`playCard`）は変えない。払う `Payment` が、カードの費用を払うか、費用に追加コストを足したものを払うかで、どちらを選んだかが決まる（総額が必ず違うので、曖昧にならない）。
- **追加コスト**（`CardDef.extraCosts`、`playCosts`、`paysFor`、`playPayments`、`paidExtra`）: Accelerate を持つ Unit は、1 Energy と自分のドメインの Power（`.own`）を足せる（CR 805）。Repeat を持つ Spell は、キーワードの費用を足せる（CR 820）。`Cost.plus`（`total_plus`）。合法の判定（`playable`、`castable`）と、列挙（`legalPlays`）は、この費用の一覧を使う。同時に 2 つの追加コストを払うことはできない。
- **効果**: Accelerate で払うと、Unit は ready で入る（`applyPlay`）。Repeat で払うと、Spell を Chain に載せるときに `Object.repeated` を立て、解決のとき、効果を 2 回続けて実行する（`resolveFrames`）。選んだ対象は 2 回とも同じ。
- **I8 の言い直し**: 「費用をちょうど払う」は、「費用、または費用に追加コストを足したもの（`playCosts` の 1 つ）をちょうど払う」になった。`applyPlay_unit_exhausted` は、追加コストを払っていないことを仮定する。
- **テスト**（`RiftboundTest/Optional.lean`）: Pool が足りるときだけ追加コストの払い方が合法の手に出ること、Accelerate は払えば ready で入り払わなければ exhausted で入ること、Repeat は払えば手札が 1 枚多く増えること（効果が 2 回）。期待を間違えると失敗することも確かめた。
- **ビューア・デモ**: トレースに `pay`（払った総額）が入り、ビューアは費用より多く払ったとき「追加コスト +N」と出す。デモの Spark に Repeat 1 Energy、Pinger に Accelerate が付く。デモの Player は、Rune を先に exhaust して、同じカード・同じ対象の手のうち、払う額が最大のものを選ぶ。seed 2 の 32 番で Spark の効果が 2 回（`damaged` が 2 つ）、425 番で Pinger が ready で入る。
- **まだ無いもの**: 「次の Spell は Repeat を持つ」などの付与、Repeat の費用が Discard のもの、Repeat で選び直す対象（「may make different choices」）、Accelerate の付与（「Friendly units played from anywhere other than hand have Accelerate」）、Repeat の費用の軽減。
- **次の候補**: Hidden（50 枚）、Empower（47 枚）、Flow（17 枚）。

### M7i の実装の記録（2026-11-22）: Deflect

- **計画からの変更**: 前の報告では「行動に追加コストの項を足す」と書いたが、**追加コストの Power を、行動の払い方に足さず、Pool から自動で払う形にした**。行動に項を足すと、`playCard`、`activate`、`putTrigger` の 3 つの行動の型と、合法手の列挙・I8（費用をちょうど払う）・各不変条件の腕が連鎖して変わる。自動で払えば、合法かどうかの判定（`castable`、`activatable`、`trigLegal`）と、答えを適用した後の 1 か所（`applyFrame`）だけで済む。代わりに、**どの Power で払うかをプレイヤーが選べない**（モデルの決定）。
- **効果を持つカード**: Deflect を印刷したカード（転記済みの 31 枚）と、Equipment が与える Deflect。todo のカードは、転記されるまで動かない。数は増えない（すでに「IR で書けた」に数えている）。
- **Deflect**（`Rules/Deflect.lean`: `deflectOf`、`deflectCost`、`deflectOk`、`paySurcharge`）: 相手が、Spell・起動型能力・誘発能力で、Deflect X を持つ Unit を対象に選ぶとき、追加コストとして任意ドメインの Power を X 払う（CR 809）。X は、印刷された値と、Equipment が与えた値の合計。数のない Deflect は 1。同じ Unit を 2 回選べば 2 回払う。自分の Unit には払わない。
- **合法の判定**: `castable`、`activatable` は、印刷された費用を払った後の Pool が、`deflectCost` を払えることを求める。誘発能力は、`trigTuples`（払える対象の組だけ）を使い、払える組が無ければ、対象を選ばずに取り除かれる（CR 355）。
- **払い方**（`RunePool.takeN`）: ドメインの Power を先に（`fury`、`calm`、`mind`、`body`、`chaos`、`order` の順）、任意ドメインの Power を最後に取る。柔軟な Power を残すため。`paySurcharge` は `applyFrame` の中で、答えの後の状態の Pool を変える。
- **証明**: `total_takeN`（n 個取ると、ちょうど n 減る）、`paySurcharge_cases`（何も変えないか、1 人の Pool だけを変える）。`PoolStep` で、Pool の変更が `WF`、物理カード、`OwnerOk`、スタックを保つことを示し、不変条件の `applyFrame` の 7 か所（Step、Sound、Progress、Resources、Setup、Hands）に、数行ずつ足しただけで保たれた。**進行の定理は、払えない対象を選ぶ手が無くなっても、`trigLegal_exists`（取り除く手がいつも合法）で保たれる**。
- **テスト**（`RiftboundTest/Deflect.lean`）: `deflectCost`（相手のみ、2 回選べば 2 倍、自分は 0）、Spell（Power が足りないと合法でなく、足りると合法で、通すと Pool が空になる）、自分の Unit は Energy だけで足りること、`takeN` の順序、起動型能力、誘発能力（払えなければ対象なしの 1 手だけ）。
- **ビューア・デモ**: デモのデッキに Guardian（Deflect 1 の Unit、Quick Study の代わり）が入る。seed 1 の 164 番で、P1 が Counterstrike（費用 1）で P0 の Guardian を対象にし、Pool が 7 から 5 になる。
- **まだ無いもの**: 払う Power の選択（行動に払う Power の項を足す）、Equipment 以外が与える Deflect（「Friendly buffed units have Deflect」など）。
- **次の候補**: Accelerate（32 枚）、Repeat（24 枚）、Hidden（50 枚）、Empower（47 枚）。

### M7h の実装の記録（2026-11-22）: Temporary と、キーワードの意味の洗い出し

- **おすすめの変更（データで確かめた結果）**: 前の報告では「起動型能力の費用を広げる」をおすすめしたが、費用が語になっている起動型能力の行を数えると、効果まで書ける行は十数行（Spend N XP が 2、Kill this が 3、Disempower が 5、Discard が 1 など）で、1 回の PR で増えるカードが少なかった。そこで、**キーワードの意味がエンジンに入っているかを洗い出し**、枚数の多い Temporary を先に入れた。
- **洗い出しの結果**（データの文に `[キーワード` が出るカード数。エンジンに意味がある: Reaction・Action・Assault・Shield・Ganking・Tank・Hunt・Level・Equip、Deathknell は誘発として書ける）: **意味がまだ無い**のは Deflect 52、Hidden 50、Empower 47、Accelerate 32、Repeat 24、Temporary 24（今回）、Flow 17、Ambush 15、Weaponmaster 12、Legion 10、Vision 9、Disarm 9、Quick-Draw 6、Backline 4。**これらのキーワードだけを持つカードは、すでに「IR で書けた」に数えているが、そのキーワードの意味は動かない**。カードの数は、意味まで動くカードの数ではない。
- **Temporary**（`Rules/Temporary.lean`: `tempUnits`、`killAll`、`beginStep`）: Beginning Phase の始まりに、ターンプレイヤーの Temporary の Unit を kill してから、Hold の得点をする（CR 816、315.2.a）。Frame を足さず、`phase .beginning` の腕の `hold` を、`beginStep`（kill してから hold）に置き換えた。`beginStep_safeP`（`SafeP`）を証明したので、不変条件の腕は `hold_safeP` を `beginStep_safeP` に直しただけで保たれた。
- **テスト**（`RiftboundTest/Temporary.lean`）: Temporary の Unit だけが見つかること、`beginStep` で kill されて Trash へ行き `died` が出ること、実際のゲームで、置いたターンの次の自分のターンの始まりに消えること。
- **ビューア・デモ**: デモの Summoner が、Recruit の代わりに ready の Sprite（3 Might、Temporary）を出す。seed 1 の 95 番で、Hold の得点より前に死ぬ。
- **まだ無いもの**: 上の一覧のほかのキーワード。Deflect（対象にする追加コスト）は、行動に追加コストの項を足す必要がある。Backline は、致死ダメージを割り当てる順序（Tank の逆）で、進行の定理の見直しが要る。
- **次の候補**: Deflect（52 枚）、Accelerate（32 枚）、Backline（4 枚）。

### M7g の実装の記録（2026-11-22）: Discard（選ぶ決定）と Channel の効果

- **何を数えたか**: 止まっている効果の部品のうち、Discard N（5 枚: 「Discard N, then draw N」）と Channel N runes exhausted（6 枚）が最も多い。Score は 3 枚だけで、点が変わる（`Safe` から外れる）ので、証明の手間に合わず後回しにした。
- **Discard は選ぶ決定**（`Frame.discard p n`、行動 `discardPick card` と `discardDone`）: プレイヤーが手札から 1 枚ずつ選び、Trash へ送る（CR 415）。手札が空か、残りが 0 のときは、終わる行動だけが合法になる。**この形にしたのは、どの局面でも合法な行動が 1 つはある、という進行の定理を、手札が足りるという新しい不変条件なしで保つため。** `Effect` の実行は、`draw` と同じく、選ぶフレームを積んでから続きを実行する。
- **Channel の効果**（`channelEx`、`channelAll`、`channel_safe`）: 毎ターンの Channel の関数を使い、指定した数の Rune を ready で、さらに指定した数を exhausted で出す。Rune が足りないときは、ある分だけ（CR 431.3）。
- **転記**: 「A, then b.」を 2 つの文に分ける（順番は同じ）、`Discard N`、`Channel N rune(s) (exhausted)`、「…exhausted and draw N」。**転記済みは 191 枚から 202 枚**。
- **証明**: `applyFrame0` の新しい腕を、Step / Sound / Hands / Progress / Setup の不変条件に足した（`sendObj_safe` を使う）。`Progress` は、`discard` フレームが決定フレームとして合法な行動を持つことを足した。`Frame.isPlay` に `discard` を含めたので、Hands の「セットアップ中は無い」の条件がそのまま効く。
- **テスト**（`RiftboundTest/Discard.lean`）: 捨てる決定が手札のカードだけを挙げること、選ぶと Trash が 1 枚増えてから引くこと、空の手札と n = 0 では終わる行動だけになること、Channel の効果で Rune が出て exhausted になること。
- **ビューア・デモ**: 「捨てる」の行動が出る。デモのデッキに Looter（出たとき、1 枚捨てて 1 枚引く Unit）が入る。
- **まだ無いもの**: 費用としての Discard（Chain を通る起動型能力で、どのカードを捨てるかを払う前に選ぶ）、「Each player discards」「捨てたカードの種類で分かれる」文、`Score` の効果、「できなかったなら」の条件つきの文。

### M7f の実装の記録（2026-11-22）: Gold トークンと「Kill this」の費用

- **おすすめの変更（データで確かめた結果）**: 前の報告では「Spend N XP などの費用を広げる」をおすすめしたが、残りの文を数え直すと、Spend N XP は 7 行、Spend a buff は 2 行で、1 回の PR で増えるカードが少ない。いっぽう **Gold トークン**（Gear。「Kill this, Exhaust: Add 任意の領域の Power 1」）を作る文は 8 枚あり、M7e の Add 能力と合わせるとそのまま書ける。そこで、費用の拡張は「Kill this」だけにして、Gold を先に入れた。
- **「Kill this」の費用**（`AbilityCost.killSelf`、`manaPlan`、`killNow`）: Add 能力の費用に、自分を kill することを足した。Add は Cleanup を通らないので、トークンが Board を離れて消える手順（`tokenStep`）を、その場で行う（`killNow`、`killNow_safe`）。起動型能力（Chain を通るもの）の `killSelf` は、まだ払えない。
- **データが持つトークンを名前で探す**（`GameState.tokenCard`）: `create` は、まずモデルが決めた `TKN-<name>` を探し、なければデータのカード（番号に T を含む: Gold、Bird、Recruit、Reflection）を名前で探す。`Tokens.lean` から、データにある Recruit と Bird を除いた（7 → 5 種）。
- **Gold**（`SFD-T03`）: 「Kill this, Exhaust: [Reaction] Add 任意の領域の Power 1」を IR に書いた。カードが「Play a Gold gear token exhausted」と言う文を転記する型を足した（`exhausted`、`gear token`）。**転記済みは 182 枚から 191 枚**。
- **証明**: `tokenStep_safe`（`cleanupStep_safe` から切り出した）、`killNow_safe`、`applyMana_*` を、費用の「kill」を含む形に直した。不変条件の腕は、`applyMana_meta` の形（事項が 5 つ）に合わせて直した。
- **テスト**: `RiftboundTest/Mana.lean`（Gold は Exhaust して出るので、準備できるまで使えない。使うと kill されて消え、Trash は増えない。任意の Power が 1 入る）、`RiftboundTest/Token.lean`（データのトークンが名前で見つかる）。
- **ビューア・デモ**: デモのデッキに Prospector（出たとき Gold を出す Unit）が入る。
- **まだ無いもの**: Bomb（データに文が無い）、Gold を「Chain を通る起動型能力」として払う費用（kill / Spend XP / Spend a buff / Discard / Recycle me）。

### M7e の実装の記録（2026-11-22）: Add 能力と起動型能力の転記

- **何を数えたか**: 「X: 効果」の形（起動型能力）は 75 行ほどで、費用は Exhaust（37）、Energy + Exhaust（13）、Spend N XP（7）が多い。エンジンは Exhaust と Energy / Power の費用を知っているので、転記の型を足すだけで書ける。「[Add]」は 36 行あり、起動型能力のうち最も多い失敗の理由だった。
- **Add 能力**（`Rules/Mana.lean`）: Energy か Power を Rune Pool に足す能力は、Chain を通らず、すぐ解決する（CR 430）。行動 `manaAbility source idx`（`manaReady` が合法の条件、`legalManas` が列挙、`mem_legalManas`）。起動型能力としては `activatable` が断る（二重に合法にならない）。Priority を持つとき、Chain が空でも空でなくても使える（Reaction）。対象は、Exhaust だけを払って、固定量を自分に足す能力。「Use only to play spells」のような使い道の制限つきは、まだ書かない。
- **任意の領域の Power**（`RunePool.any`）: `[Add] :rb_rune_rainbow:` は、どの領域の Power の記号も払える Power として持つ。**モデルの決定**: その領域の Power が無いときに使う（`takePower`）。公式の裁定とは照合していない。
- **転記**: 起動型能力（費用は Exhaust・Energy・Power、速さは通常・Action・Reaction）、`Kill this`、`Move … to your base`（`move` プリミティブ）、`[Add] …`。**転記済みは 166 枚から 182 枚**。
- **証明**: `applyMana_wf` ほか（Add は `Safe` な変更に Rune Pool の変更を足したもの）。`RunePool` の合計の補題（`total_takePower`）は、`any` を含めて証明した。既存の不変条件は、`runeAbility` の腕と同じ形の腕を足して保たれた。
- **テスト**（`RiftboundTest/Mana.lean`）: Add は Chain の起動型能力ではないこと、使うと Exhaust して資源が増え Chain は空のままであること、Power（領域、任意の領域）と、任意の Power で別の領域の記号を払えること、Chain に項目があるときも使えること。
- **ビューア・デモ**: Add の行動がログに出て、Pool に「任意」の欄が出る。デモのデッキに、Energy を 1 足す Gear の Battery が入る。
- **まだ無いもの**: `Spend N XP`・`Spend a buff`・`Discard`・`Recycle me` などの費用、使い道の制限つきの Add（"Use only to play spells"）、量が決まらない Add（"that much"）、Energy と Power を両方足す Add。

### M7d の実装の記録（2026-11-22）: Buff・Stun・XP

- **Buff**（CR 701）: Unit が buff を持つ（`buffed`）と +1 Might（`mightNow`）。すでに持っていれば変わらない。Board を離れると消える。
- **Stun**（CR 424）: Unit が `stunned` だと、Combat Damage を与えない（`combatMight` が 0）。ターンの終わりに消える（`endTurnObj`）。
- **XP**（CR 728）: プレイヤーの数。ゲームオブジェクトではないが、モデルは**そのプレイヤーの Legend オブジェクトに持たせる**（`Object.xp`、`xpOf`）。状態の新しい欄を足すと、状態を変えるすべての証明が `Safe` から外れるため。`gainXP` は Legend の欄を足す。Legend が無いプレイヤーは XP を得られない。
- **キーワード Hunt X**（CR 823）: 「Conquer または Hold したとき XP を X 得る」の 2 つの誘発能力に展開される（`keywordAbilities`）。**Level N**（CR 824）は、条件 `xp ≥ N` を持つ Passive として書く（`Amount.xp` を解釈器が読む）。
- **読み取り**: `Filter.stunned`・`Filter.buffed`、`Amount.xp`。`applyPrim` は `stun`・`buff`・`gainXP` を知り、安全な変更として証明した。
- **転記**: 「Buff me / a friendly unit」「Gain N XP」「[Level N][>] I have +M Might」。**転記済みは 160 枚から 166 枚**。
- **テスト**（`RiftboundTest/Status.lean`）: Buff（+1、1 回だけ、Board を離れると消える）、Stun（Combat Damage 0、ターンの終わりに消える）、XP（Legend に入る、量として読める）、Hunt の展開と Level の条件。
- **ビューア・デモ**: Stun の札に「Stun」が出る。デモのデッキに、敵を Stun する Chill と、自分を Buff する Trainer が入る。
- **まだ無いもの**: 「buff を使う」「XP を使う」コスト（`spendBuff`・`spendXP`: 起動の支払いが Energy と Power と Exhaust だけ）、「Buffs give an additional +1」のような buff を数える能力、Level の「enter ready」、Disarm、Empower。

### M7c の実装の記録（2026-11-22）: Equipment（Gear を Unit に付ける）

- **Equipment のモデル**: Gear のオブジェクトが `attached`（付いている Unit）を持つ。付いている間、Unit は Equipment の Might の加算（`mightBonus`）と、Equipment が与える能力（`CardDef.grants`: 付けた Unit に与える文）を持つ。Board を離れると `attached` は消える（`moveObj`）。Unit がいなくなった Equipment は、Cleanup の手順（`detachStep`）で外れる。
- **Equip キーワード**（`CardDef.keywordAbilities`）: `[Equip] コスト` は、「コストを払って、これを自分の Unit に付ける」起動型能力に展開される（`attach` プリミティブ）。キーワードが展開する能力は `fullAbilities`（能力 + キーワードの能力）に入り、起動の列挙・誘発・Passive の添字は、これを数える。付けた Unit に与える能力は `allAbilities` の末尾で、Chain の項目はカードの ID と通し番号を覚えている。
- **付けた Unit が持つもの**: Might（`mightNow` が `equipBonus` を足す）、キーワード（`hasKw` と `kwAmount` が、与えられたキーワードを数える: Tank・Shield・Ganking・Assault・Deflect）、誘発能力（`triggersOf` が、付いている Equipment の `grants` も見る）。Equipment 自身は、その能力を持たない。
- **転記**: 付けた Unit に与える文（`effectText`）を、Gear のカードについて書くようにした（キーワード 5 種と、既存の誘発の型）。**転記済みは 151 枚から 160 枚**。
- **証明**: `applyAttach_safe`（付けるのは安全な変更）、`cleanupStep_safe`（外す手順を含めて）。既存の不変条件は形を変えずに保たれた。
- **テスト**（`RiftboundTest/Gear.lean`）: Equip が合法（味方の Unit にだけ）、付くと Might・キーワード・誘発能力が Unit に付くこと（Equipment 自身には付かない）、Unit が消えると外れること、付け替え。
- **ビューア・デモ**: 装備を持つ Unit の札に「装備」が出る。デモのデッキに、+2 Might と Tank を与える Training Sword が入る。
- **まだ無いもの**: **Gold と Bomb（トークンの Gear）**（能力が書かれていない）、Quick-Draw（出したとき自動で付ける）、Deploy、「付けたターンだけ」の条件、他の Equipment の条件つきの文、Equipment を付ける先の制限。

### M7b の実装の記録（2026-11-22）: トークン

- **トークンの定義**（`RiftboundCards/Tokens.lean`）: Unit のトークン 7 種（Recruit・Mech・Sprite・Bird・Sand Soldier・Shadow Clone・Tentacle）。印刷される Might と、トークンが持つキーワード（Sprite の Temporary、Bird の Deflect 1）を持つ。カードの定義と同じ `CardDB` に入り（`db`）、識別子は `TKN-<名前>`。**Gold と Bomb（Gear のトークン）は、能力が書かれていないので入れていない**。
- **`create`**（`Prim.create name n place ready`）: トークンを `n` 個、プレイヤーの Base か、`here`（その Battlefield）に出す（`applyCreate`）。トークンは物理カードを持たないので、`WF`・I1・`OwnerOk` を保つ（`createN_safe`、`applyCreate_safe`）。Ready で出すか Exhaust で出すかは文に従う。知らないトークンや、まだ分からない場所（選ぶ場所）には何もしない。
- **Board を離れたトークンは消える**（CR 183）: Cleanup の最初の手順（`tokenStep`）が、Non-Board のゾーンにあるトークンを `removeObj` で消す。したがって、死んだ Unit のトークンは Trash に残らない。死んだときの誘発能力は、カードの ID を持つので、トークンが消えても解決できる。`cleanupStep_safe` は新しい手順を含めて証明した。
- **転記**: 「Play a (ready) N Might Name unit token(s) (to your base / here)」と、`[Deathknell][>]` の誘発を足した。**転記済みは 135 枚から 151 枚**（Spell で動くものは 29 枚）。
- **テスト**（`RiftboundTest/Token.lean`）: 定義、Spell がトークンを出す（Exhaust と Ready、物理カードは増えない）、`here`、知らない名前、Board を離れたトークンが消えること。Chain と Trigger のテストのうち、トークンを Spell や Unit の代わりに使っていたものは、「Trash に残らない」に直した。
- **まだ無いもの**: Gold・Bomb のトークン、トークンを出す場所の選択（Battlefield を選ぶ）、他のプレイヤーの Base、トークンのコピー、Temporary（Beginning Phase に消える）の動作。

### M7a の実装の記録（2026-11-22）: 転記の対応範囲（`here`・Move の誘発・文の型）

- **何を数えたか**: 転記が済んでいないカード 985 枚の文を調べた。1 枚の効果文のうち書けない行が 1 つだけのカードは 792 枚あるが、その行の文はほとんどが 1 枚ごとに違う（同じ型が 7 枚以上のものは「[Reaction] — [Add]」だけ）。**文の型を足して増える枚数は、1 回あたり十数枚**で、残りは 1 枚ずつ書くことになる。
- **文の型を足した**（`scripts/transcribe.py`）: 誘発の本文の頭文字を大文字にしていなかったため「When you play me, draw 2」などが合わなかったのを直した（15 枚）。「Deal N to all (friendly / enemy) units (here / at a battlefield)」「Kill all (damaged) … units」「When I move, …」を足した。**転記済みは 117 枚から 135 枚**（Spell で最初から最後まで動くものは 24 枚から 25 枚、能力を持つカードは 46 枚）。
- **エンジン**: 場所 `here`（Battlefield の自分の場所。Unit はいる Battlefield、Battlefield はそれ自身）を解釈器が分かるようにした（`placeObjs` が `self` を取る）。「here」を使う文は 168 枚のカードにある。Unit の Move は誘発する（`When I move`）。
- **テスト**（`RiftboundTest/Here.lean`）: 「here」の対象（同じ Battlefield の Unit だけ、Base にいる Unit には答えが無い）、Move の誘発。
- **まだ無いもの**: トークンを作る文（105 枚のカードにある）、Buff・Stun・XP・Channel・Score の文、複数の対象、条件つきの文、キーワードを与える文。それぞれ、エンジンの機能が先に要る。

### M6e の実装の記録（2026-11-22）: Passive 能力（場に出たとき Ready、Might の変更）

- **データを見て範囲を決めた**: 全カードの効果文を数えると、最も多いのは「場に出たとき」の誘発（188 行）で、その次が Passive の「I enter ready」（17 行）、「[Empowered] I have +N Might」（19 行）、「I cost less」（11 行）だった。転記済みのカードの Passive は少ないので、仕組み（`Rules/Passive.lean`）を作り、よく出る 2 つを動かした。
- **`entersReady`**: 条件なしの Passive `entersReady .self` を持つ Unit は、Ready で場に出る（CR 359 の例外）。`applyPlay_unit_exhausted` は「`entersReady` が無い Unit は Exhaust で入る」になった。
- **Might の導出**（`mightNow`）: 印刷された Might + 持続する変更（M6d）+ Passive の変更。Passive は、場にある Unit と Legend の `Ability.passive cond mods` のうち、条件が成り立つもの。`mightPlus` と `mightMinus` を、選択子が指すオブジェクトに足す。**致死ダメージと Combat は `mightNow` を読む**。選択子と条件が読む Might（`Filter.might`）は `mightOf`（Passive を含まない）のままで、Passive どうしが依存しない（Layers の最後の層に Arithmetic が来る: CR 479.4。依存の整理（CR 480-481）は、必要なカードが来てから）。
- **テスト**（`RiftboundTest/Passive.lean`）: 場に出たとき Ready か Exhaust か、味方の Unit に +1 を与える Unit（自分と相手には効かない、場を離れると消える）、致死ダメージと Combat が変更後の Might を読むこと、Rune の数による条件、Might が下がる Passive、手札の Passive は効かないこと。
- **ビューア・デモ**: 札の `+N` は、持続する変更と Passive の合計。デモのデッキに、味方を強くする Banner と、Ready で出る Scout が入る。
- **まだ無いもの**: `here` の場所を使う Passive、Empowered の状態、`costMinus`・`bonusDamage`・`victoryScorePlus`・`triggersExtra`・`cantPlayer`・`ignoreKeyword` などの hook、キーワードの付与、Layers の順序と依存。

### M6d の実装の記録（2026-11-22）: 持続する Might の変更（Layers の最初の一歩）

- **方針を変えた**: 前の報告のおすすめは「Spell のモード・X・複数の対象・`may`」だったが、転記済みの Spell 34 枚を調べると、モードや X を使うものはほとんど無く、動かない 18 枚の主因は**持続する Might の変更（`grant`）**だった。そこで先にこれを入れた。選択のフレーム（モード・X・`may`）は、それを使うカードが転記されたときに足す。
- **仕組み**: Object に `mightMods`（変更の量と、いつ終わるか）を持たせた。`grant sel (mightPlus / mightMinus .it a) d` は、選んだ各オブジェクトに変更を足す（`applyGrant`）。`mightOf`（Might を読む唯一の入口）は、印刷された Might と変更の合計になった。したがって、致死ダメージ、Combat の合計と致死に要る量、効果の `Filter.might` が、すべて変更後の Might を読む。
- **期限**: `thisTurn` はターンの終わり（Ending）に消える（`endTurnObj`）。`permanent` は消えない。Board を離れると消える（`moveObj`）。`thisCombat`・`thisShowdown`・`whileCond`・`nextTurn` はまだ（解釈器は飛ばす）。
- **証明**: `applyGrant_safe`（変更の追加は安全な変更）。`Safe` に載るので、既存の不変条件は数行の変更で保たれる（`endTurnObj_kind`・`endTurnObj_owner`）。
- **効果**: 動く Spell が 16 枚から 24 枚に増えた（`grant` を使う 8 枚）。
- **テスト**（`RiftboundTest/Might.lean`）: +3 の Spell で Might が 5 になる、他の Unit は変わらない、ターンの終わりで消える、`permanent` は残る、-10 で 0 以下になる、`Filter.might` が変更後を読む、Board を離れると消える、期限が `thisCombat` の変更は解釈器が知らない。
- **ビューア・デモ**: 変更のある札に `+3` が出る。デモのデッキに、味方の Unit に +3 Might を与える Surge が入る。
- **まだ無いもの**: `Ability.passive` の Might の変更（Master Yi の「Rune が 8 枚以上のとき +4」など。条件の評価が Might を読むので、依存関係の整理が要る）、キーワードや能力の付与、Controller の変更、Layers の順序（timestamp と依存）、コピー。

### M6c の実装の記録（2026-11-22）: 誘発の順序と対象の選択

- **決定のフレーム `triggerOrder`**（行動 `putTrigger idx targets`）: 同じプレイヤーの待っている誘発能力から 1 つを選んで Chain に載せ、その対象も選ぶ（CR 383.3.d, 355）。残りは `triggers` に戻り、また選ぶ。最後に載せたものが上になり、先に解決する。選ぶものが無い 1 つの能力（対象なし）は、決定なしで載る。手番のプレイヤーの能力から先に載せる。
- **対象を取る誘発能力が動く**: M6b では「対象が要るので誘発しない」としていたものが、対象を選んで載る。合法な対象が無いときは、対象なしの答えだけが合法で、その能力は取り除かれる（CR 355）。
- **証明**: `trigLegal_exists`（待っている能力には必ず合法な答えがある）から、I5（行き止まりが無い）を `triggerOrder` について証明した。`mem_trigOptions`・`mem_legalPuts`（列挙は合法な答えだけ）。`putPick_safe`・`triggersStep_spec`（`triggers` の 1 歩は安全な変更で、積むのは Chain の Priority と `triggers` と `triggerOrder` だけ）から、`WF`・I1・`OwnerOk`・`StackInv`・`HandInv`・`SetupInv`・`step_sound`・`legalActions_iff` を新しい行動とフレームを含めて保つ。
- **テスト**: 対象つきの誘発（唯一の合法な答え、載った対象、解決）、合法な対象が無いときに取り除かれること、複数の能力の順序の選択（最後に載せたものが上）。
- **ビューア・デモ**: `putTrigger` がログに出る。デモのデッキに、場に出たとき敵の Unit に 1 ダメージを与える Archer が入る。
- **まだ無いもの**: 複数の対象、モード、X、`may`、追加コスト（Spell と能力の選択）、対象が 1 つで決まるときの自動化、自分以外が対象の誘発。

### M6b の実装の記録（2026-11-22）: 誘発型能力（最小版）

- **誘発の検出**（`Rules/Trigger.lean`）: `microStep` と `applyFrame` を「ステップ本体（`microStep0`・`applyFrame0`）+ `withTriggers`」に分けた。`withTriggers` は、その歩のイベントを読み（`detect`）、誘発した能力を `triggers` のフレームとして、Cleanup や解決の作業の下に積む。Priority が次に渡る前に Chain へ載る（CR 383.1）。セットアップの間は何もしない。
- **イベント**: `played`（カードのプレイ）、`died`（`killObj`: Cleanup の kill と `kill` の効果）、`combatStarted`、既存の `scored`。誘発の種類: play・die・conquer・hold・youConquer・youHold・attack・defend。
- **載せる**（`triggers` フレーム）: 能力は Chain 上のオブジェクトになり（M6a と同じ）、解決は既存の経路。載せた後に Chain に項目があれば、手番のプレイヤーが Priority を持つ。手番のプレイヤーの能力から載せる（CR 383.3）。
- **証明**: `microStep` と `applyFrame` の包みについて、`WF`・I1・`OwnerOk`・`StackInv`・`HandInv`・`SetupInv`・`step_sound`・`legalActions_iff`・I5 を、`withTriggers` が `pending` だけを変え、積むのは `triggers` のフレームだけであることから導いた（`insertTriggers_mem`・`insertTriggers_getLast`・`withTriggers_cases` ほか）。
- **テスト**（`RiftboundTest/Trigger.lean`）: 場に出たとき、死んだとき、Conquer、Combat の attack / defend、Legend の youHold、手番のプレイヤーが先、1 ターン 1 回の制限、対象が要る能力は誘発しないこと。
- **まだ無いもの**: 同じプレイヤーの能力の順序の選択（383.3.d）、対象とモードを取る誘発能力、subject が自分以外の誘発（「ユニットをプレイしたとき」など）、条件つきの誘発、フェイズの区切りの誘発（`at_`）、`enter`・`move`・`leave` などの種類、キーワードの Deathknell・Vision などの展開、Reflexive Trigger。

### M6a の実装の記録（2026-11-21）: Chain に複数の項目、Reaction、起動型能力

- **M6 を分けた**: M6a は起動型能力と、複数の項目が載る Chain と Reaction（この記録）。誘発型能力、Replacement、Layers は M6b 以降。
- **Chain の項目**: Spell（カードのオブジェクト）と、起動した能力（`ObjKind.chainAbility card idx source`）。能力は Chain ゾーンの上に載るオブジェクトで、物理カードを持たない。カードの ID を持つので、元のオブジェクトが場を離れても解決できる（Last Known Information）。解決すると `removeObj` で消える（`Rules/Remove.lean`）。解決の後に項目が残っていれば、手番のプレイヤーが Priority を持ち直す（`afterItem`）。
- **起動型能力**（`activate source idx pay targets`、`Rules/Chain.lean`）: 支払えるコストは、自分の Exhaust と、Energy と Power（`costPlan`）。それ以外のコストを持つ能力は、まだ使えない。`activatable`（合法）、`applyActivate`、`legalActivates`（列挙）、`mem_legalActivates`。速さ: Chain が空のときは、どの速さでも起動できる。Chain に項目があるときは Reaction だけ（CR 813）。1 ターンの回数制限（`Limit.perTurn`）は `Object.used` に数える（ターンの始まりに消す）。
- **Reaction**: Chain に項目がある間（`chainPass`）、Reaction を持つ Spell を唱える（`reactable`、`legalReactions`）、速さが Reaction の能力を起動する、Basic Rune の能力で資源を出す、ことができる。唱えたり起動したりすると、項目が上に積まれ、その人から Priority が回り直す。
- **証明**:
  - **I9（Chain は後入れ先出し）**: `applyActivate_chain`・`applyCast_chain`（項目は Chain ゾーンの先頭に載る）、`resolveFrames_top`（解決するのは先頭の項目）、`finishItem_top_chain`（解決すると残りは `more`）。
  - `removeObj_wf`・`removeObj_physIds`・`removeObj_ownerOk`、`addObject_physIds`: 物理カードを持たないオブジェクトの追加と除去は、`WF`・I1・`OwnerOk` を保つ。
  - 新しい行動（`activate`、Chain にあるときの `playCard`・`runeAbility`）について、`WF`・I1・`OwnerOk`・`StackInv`・`HandInv`・`SetupInv`・`step_sound`・`legalActions_iff`・I5 が成り立つ。`activateStep_*` と `castStep_*` に 1 本ずつの補題を束ねたので、各不変条件への追加は数行で済んだ。
- **テスト**（`RiftboundTest/Chain.lean`）: 起動の合法・違法（制御者、対象、フェイズ、支払い）、能力が Chain に載ること（対象、物理カードは変わらない）、2 人がパスして解決し能力が消えること、Reaction の能力と Spell で応答し、上の項目から先に解決して、残りの項目を手番のプレイヤーが続けて解決すること、元のオブジェクトが消えても解決すること、`perTurn` と支払い、使えないコスト、列挙したものはすべてエンジンが受け付けること。
- **ビューア**: 起動の行動、Chain 上の能力（点線の札）、Reaction でのプレイがログに出る。デモのデッキに、Exhaust で敵の Unit に 1 ダメージを与える Unit（Pinger）と、Reaction の Spell（Counterstrike）が入る。デモの対戦相手は、Reaction のために Rune を 1 枚残す。
- **まだ無いもの**: 誘発型能力（M6b）、Action の速さの Spell と Showdown の中での Action と Reaction、Chain に項目があるときの Standard Move、自分の Exhaust と Energy と Power 以外のコスト（捨てる、Recycle、XP、Buff など）、Add 能力が Chain を通らず即座に解決する規則（430.2 のうち Rune の能力以外）、`may` と複数の選択（選択のフレーム）、効果の解決中の Reflexive Trigger、能力のコピー、解決時に項目が失敗する場合（`finishItem_top_chain` は「解決できなければ何も変わらない」の枝を含む）。CR / TR の番号は公式 PDF と照合していない。

**実装**
- Passive（363-366）。
- Replacement（367-375）: イベントの経路の置換の段（M2 で作ったもの）に、カードの置換効果と Prevent（438）を足す。適用順は 372、1 つのイベントに同じ置換は 1 回まで（370.2）。
- Triggered（382-385）: 同時に誘発したものの順序（383.3.d）と、戦闘開始時の例外（466.2.d.1）。順序は「次に積む能力を選ぶ」決定の列にする。
  - 導出値への誘発（「Mighty になったとき」: 709）は、1 歩の前後の `characteristics` を比べて検出する（[design.md §5.4](design.md#54-特性の導出layers)）。
- Reflexive、Delayed、Linked（387-398）。
- **Layers**: Copy → Trait → Ability → Arithmetic（479）。変化がなくなるまでの反復（478.2-478.3）。反復の上限は内側で決め、外から fuel を受け取らない。同一層内は timestamp 順（482）。M5 の暫定版を差し替える。依存関係（480-481）は、それが必要なカードが来た時点で入れる。
  - 実効の Controller は Trait 層で決まる。規則の判定は、表の基底の値ではなく実効の値を使う（[design.md §5.2](design.md#52-ゾーンとオブジェクト)）。
- hook を `StaticMod` で埋める（[design.md §7.3](design.md#73-ルールの差し込み口hook)）。
- 残りの Origins 期のキーワード: Accelerate、Deathknell、Deflect、Hidden、Legion、Temporary、Vision。
  - Action と Reaction は M4、戦闘のものは M5 で実装済み。

**証明**
- 置換効果は、1 つのイベントに対して同じものが高々 1 回しか適用されない（370.2）。
- キーワードの意味の補題。例: Assault X は Attacker である間だけ Might を X 増やす（807）。
- Arithmetic 層では、増加が減少より先に適用される（479.4.e）。
- 能力系のフレーム（誘発の順序、置換の順序）について I6。

## M7: Origins・Proving Grounds の全カード

**前提**: M3b で、取り込みのパイプラインと、構文だけの転記が済んでいる。

**実装**
1. **棚卸しの仕上げ**: M3b の一覧を見直す。Origins と Proving Grounds の全カードが要求するプリミティブ・結合子・hook のうち、まだ意味の無いもの（Discard、Reveal、Double、Swap、Detach、Prevent など）に意味を与える。
2. 実装カバレッジ表と、`custom` のハンドラ表を整える。
3. Origins（通し番号上 298 種）と Proving Grounds（24 種）のカードを、`drafted` から `full` にする。転記を見直し、シナリオテストを書く。
4. 公式 FAQ の裁定を回帰テストにする。

**証明（L4）**
- 新しく足したプリミティブについて、`WF` 保存の補題を足す（L4 を広げる）。
- 具体的な `CardDB` が `CardDB.WF` を満たすことを検査する（参照する Tag・Keyword・custom ハンドラが定義済みであることなど）。

## M8: 後続セット（セットごとの小マイルストーン）

各セットで「棚卸し（構文だけの転記）→ 新しいキーワード・プリミティブ・hook → カード → テスト」の順に進める。手順は [card-data.md](card-data.md) に従う。

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
- 投了による除去（投了後に 2 人以上が残る場合: 651.2, 652。2v2 ではチーム全員が敗北: 651.4）。ゲームから取り除く物理カード（置き換えられた Battlefield など）は `outOfGame` に置き、I1 を保つ。
- 2v2 固有の規則（得点の共有、味方の招待、Final Point の調整など: 491.8）。大会の 2v2 の席順と手番順（TR 603.7）。
- ObjId と timestamp の付け替えを無視した、状態の同値を定義する。`view` とループの検出器が共有する。
- `view` を完成させる。
- ループの検出器（`Tournament/LoopDetect.lean`）: 決定点をまたいで、強制的なループを検出する（[tournament-model.md §5](tournament-model.md#5-ループtr-505)）。Driver が使い、検出したらジャッジの `Action` を送る。
- M8 までに `partial`（多人数の仕組み待ち）としたカードを `full` にする。

**証明（L6）**: I10、I19。

## M10: 完了判定（original.md の最終目的）

次をすべて満たしたとき、その時点のカードプールについて R5（[design.md §1](design.md#1-要求の整理)）を達成したとみなす。

1. 公開済みの全セットで、全カードの `ImplStatus` が `full` である。
2. `custom` ハンドラの一覧があり、それぞれにシナリオテストがある。
3. `Legal` が全フレームの種類を覆い、全種類について I6 が証明されている。
4. I1〜I19 が証明されている。I12 のうち fuel で扱う部分は、その範囲を明記している。
5. [tournament-model.md](tournament-model.md) の対象範囲（フォーマット、マッチ、時間切れ、ループ、合意の引き分け、2v2 の席順）が実装されている。
6. 全体の検証（`scripts/verify.sh`: build、test、axiom の監査、カードデータの陳腐化検査）がローカルで通る。

証明（3 と 4）を完了条件に含めることは、決定済みである（[design.md §12](design.md#12-決定事項2026-11-20) Q6）。

以後は継続作業になる: 新しいセットの追加（M8 と同じ手順）、関係仕様（L5）の拡充（コスト計算 356、Layers 478-482）、性能改善、CLI。

---

## 実装状況（ImplStatus）の定義

- `todo`: メタデータのみ。
- `drafted`: 効果を IR の値として転記済み。意味の確認（解釈器での実行とシナリオテスト）はまだ（M3b）。
- `partial`: 一部が未実装。理由を docstring に書く（例: 多人数の仕組みを待っている場合は `needs-M9`）。
- `full`: その時点で実装済みのモードすべてで、カードの文面どおりに動く。

## 1 枚のカードの完了条件

1. 生成ブロック（公式文面の docstring とメタデータ）が最新である（`RiftboundCards/<Set>.lean`。全体の検証 `scripts/verify.sh` で確かめる）。
2. 効果が IR で書かれている。`custom` を使う場合は、ハンドラにシナリオテストがある。
3. 実装状況が `full` である。
4. シナリオテストが 1 つ以上ある。
5. 公式 FAQ・エラッタがあれば、それを反映した回帰テストがある。

**キーワードだけのカード**（効果の文が無いもの）は、2 と 4 を免除する。持っているキーワードすべてに意味の補題とテストがあれば、生成だけで `full` にしてよい。
