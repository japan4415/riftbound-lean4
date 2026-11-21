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
| I12 | **自動処理の停止**: 到達可能な状態では、Cleanup の反復・Expiration のループ・効果の解決が、有限の歩数で次の決定点に達する（ある fuel で `step` が fuel 切れにならない）。言えない部分は、fuel で扱っていることを明記する。Layers の反復は、内側の上限で必ず止まる（[design.md §5.4](design.md#54-特性の導出layers)） | L2 | M5〜 |
| I13 | **大会のデッキと Core Rules のデッキ**: Constructed で合法なデッキからサイドボードを除いたものは、Battlefield を 3 枚求めるモード（1v1 Duel など）の Core Rules のデッキ構築でも合法である（TR 402.1, 601 と CR 103）。Battlefield の枚数はモードが決めるので（CR 103.5）、モードを限定して述べる | L0 | M1 |
| I14 | **時間切れ後の終了**: 時計が時間切れを知らせた後、ゲームは有限のターン数で終わる（追加 3 ターンの後に点差で決まる: TR 408.2） | L2 | M5b |
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
