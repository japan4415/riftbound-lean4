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
| I6 | **`Legal` との一致**: `legal_of_step_ok` は成功した `step` が合法であること、`step_sound` は整形性と所有者の不変条件の下で合法手が失敗する場合の理由が fuel 切れに限られることを示す。`legalFrameActions_iff` は現在の全フレームを場合分けし、`legalActions_iff` は投了を含むプレイヤーの合法手と列挙が一致することを示す。偶然・時計・ジャッジの答えは `Legal` で判定する（[design.md §6.3](design.md#63-できること全ての担保)） | L3 | M2（マリガンと偶然の決定）から、フレームの種類ごとに |
| I7 | **勝者の一意性**: 全対戦相手より得点が多い側は高々1つ。Duel と FFA では1人、2v2 では1チームが勝つ（CR 323.1, 491.6）。`win_condition_unique`、`winner_spec`、`win_side_unique` で証明した | L2 | M5 |
| I8 | **資源の会計**: Rune Pool は負にならない。Channel と Recycle の間で Rune の総数が保存される。M3 後半で証明（`RunePool.total_spend`、`applyRune_adds_one`、`applyRune_recycle_zones`、`channelOne_zones`） | L1 | M3 |
| I9 | **ターン構造**: フェイズの順序が固定されている（M3 前半で証明: `turnPhases_chain`、`microStep_phase`）。Chain は後入れ先出し（340.1。M6a で証明: `applyActivate_chain`・`applyCast_chain`・`resolveFrames_top`・`finishItem_top_chain`）。Discretionary Action は Priority を持つプレイヤーだけが行える（312.1） | L2 | M3〜M6a |
| I10 | **隠れ情報の非干渉**: プレイヤー p の合法手は `view p s` にだけ依存する（偶然の決定を除く。ObjId の付け替えに対して不変な形で述べる）。[Visibility.lean](../Riftbound/Spec/Visibility.lean) で山札、相手の手札、他のプレイヤーが支配する伏せ札の表面が通常の射影に含まれないことを証明した。効果の解決中にフレームが保持する公開札、山札の閲覧、Predict を `resolutionZoneCardFaces` に反映した。公開・閲覧イベントの発生時に表面を記録し、リプレイから席別の履歴を出力できる。[PlayerView.lean](../Riftbound/Spec/PlayerView.lean) で席別に盤面を射影し、開示されていない山札と他席の手札が枚数だけを表すこと、およびオブジェクトの参照先が公開ゾーンに限られることを証明した。対局全体の席別盤面を JSON に出力できる。別のゾーンに開示がある場合も、対象ゾーンに開示されたカードがなければ見え方は変わらないと証明した。[PrivateChoices.lean](../Riftbound/Invariant/PrivateChoices.lean) で、マリガンと通常の捨て札では、当事者から同じ手札に見え、選択枚数が同じなら、カードごとの選択肢と終了の可否が同じになることを証明した。同じカードが複数ある場合も、選択できる枚数が一致する。Predict では各手が当事者に開示された候補だけを参照し、候補の ID を付け替えても上に戻す手とリサイクルする手が対応することを証明した。 対象プレイヤーが公開した手札から選ぶ効果では、提示された合法手が公開済みのカードを指し、その表面を選択する席が閲覧できることを証明した。カード種別を推測する手とカード名を指定する手は、非公開カードや解決中の内部参照を変えても一致する。 投了が可能な席は公開されている対戦モードと離脱済みの席で決まり、現在の選択と勝敗が一致すれば投了を含む全合法手の一覧も一致する。 戦闘ダメージの割り当てでは、候補と割り当て済みの Unit、各候補の支配者と割り当て優先順位が対応すれば、識別子が異なっても選択肢は対応する。Basic Rune の合法な起動は Base の並びと公開される所有者、Rune の領域、Ready 状態に従い、識別子を付け替えても対応する。 全種類の合法手と ID の付け替えに関する一般証明は残っている | L6 | M9 |
| I11 | **Score の回数制限**: 1 人のプレイヤー（2v2 ではチーム）は、1 つの Battlefield を 1 ターンに高々 1 回 Score する（472, 491.8.b）。同じ Battlefield に対する連続した `scoreBf` では、同じ席の2回目（`scoreBf_twice`）も味方の2回目（`scoreBf_twice_side`）も得点しないと証明した | L2 | M5 |
| I12 | **自動処理の停止**: 到達可能な状態では、Cleanup の反復・Expiration のループ・効果の解決が、有限の歩数で次の決定点に達する（ある fuel で `step` が fuel 切れにならない）。言えない部分は、fuel で扱っていることを明記する。Layers の反復は、内側の上限で必ず止まる（[design.md §5.4](design.md#54-特性の導出layers)）。連続する Cleanup の停止は、イベント処理・同時撃破・入れ子の死亡置換を含む実際のエンジン上で証明済み。登録済みカードでは、通常の優先権での合法な Pass から、即時 Add やターン移行を含めて次の決定点か試合終了まで停止を証明済み。初期手札・対局中のドロー・通常の誘発キューの上限も証明済み。繰り返しなどの制御構文と即時 Add が実行するルール処理の有限性も証明済み。Chain の最後の Pass は、対応する Run 命令列、Recycle、Cleanup、後続の保留 Spell の宣言確定を経て次の決定点に着くことを証明済み。直接・相互・振り分けダメージと、その置換選択も Chain の検査に含む。Chain での任意効果・分岐・対象の回答は、回答で生成される命令列を検査し、次の決定点に着くことを証明済み。個別の選択を記録した Repeat では、実行ごとにその時点の盤面を使って対象を再検査する。Showdown の最後の Pass と Combat の割り当て確定は、置換・割り当ての選択か、戦闘後の Cleanup を経て次の決定点に着くことを証明済み。誘発の支払いの準備・確定・取り消しと、対応する死亡置換の回答後の再開も証明済み。カードのプレイと能力起動、対応する死亡置換の回答、Recycle の対象と順番の回答も、対応する継続について次の決定点まで追える。通常移動、グループ移動、Showdown の戦場選択、対応する Cleanup への回答についても次の決定点まで証明した。Rune と即時 Add の合法な起動も、通常の優先権で Add 後に行う Cleanup を含めて証明済み。Predict の途中の入力と最終回答、カード名の指定、カード種別の推測についても、対応する継続が次の決定点に着くことを証明済み。War の対応する投了、Showdown の途中の Pass、2 対 2 の招待・辞退、Combat の割り当てでの Unit 選択も含む。次の決定点までの証明範囲は [termination.md](termination.md) に記載。 | L2 | M5〜 |
| I13 | **大会のデッキと Core Rules のデッキ**: Constructed で合法なデッキからサイドボードを除いたものは、Battlefield を 3 枚求めるモード（1v1 Duel など）の Core Rules のデッキ構築でも合法である（TR 402.1, 601 と CR 103）。Battlefield の枚数はモードが決めるので（CR 103.5）、モードを限定して述べる | L0 | M1 |
| I14 | **時間切れ後の終了**: 時計が時間切れを知らせた後、ゲームは有限のターン数で終わる（追加 3 ターンの後に点差で決まる: TR 408.2） 。局所の事実（`three_more_turns`、`beginTurn_ends`、`beginTurn_next`）に、**全体**（`Reachable.clockOk`、`step_keep`、`time_called_bound`）を足して**証明済み** | L2 | M5b |
| I15 | **fuel の単調性**: `step n db s a = .ok r` かつ `n ≤ m` なら、`step m db s a = .ok r`。fuel 切れ以外のエラーも、fuel によらない | L3 | M2 |
| I16 | **Priority の受け渡し**: [Priority.lean](../Riftbound/Invariant/Priority.lean) で、最後のパスまでは `step` が手番順で次のプレイヤーの `chainPass` に停止し、最後のパスで Chain の先頭を解決するフレームに進むと証明した。席順が全席の並べ替えであれば、一巡で全席を重複なく回る（338.2, 339, 340） | L2 | M4 |
| I17 | **`priority` の時点で `Settled`**: `priority` フレームが先頭にある全ての到達可能な状態で、Cleanup が不動点に達していることを `Reachable.priority_settled` で証明した（CR 322-323）。初期フレームには通常の優先権がなく、最初のターンでは Awaken が通常の優先権より先にセットアップを終える。エンジンは通常の優先権の直前に勝者判定と盤面を確認し、処理が残っていれば Cleanup を先に行う。[SetupPriority.lean](../Riftbound/Invariant/SetupPriority.lean) · [Priority.lean](../Riftbound/Invariant/Priority.lean) | L2 | M5 |
| I18 | **任意の選択は必ず問われる**: 解決中の選択は決定フレーム、プレイ時の追加コストなどは `Action` で受け取る（[design.md §3](design.md#3-設計原則) の P4）。[Choices.lean](../Riftbound/Invariant/Choices.lean) で、実行可能な `may`、明示的な対象選択、複数の効果の選択、任意の誘発、印刷された Spell の任意追加コストを局所的に証明した。直接プレイを受け付ける全フレームで、任意のディスカードを見送る手と、支払いに使える各手札を選ぶ手が列挙されることを証明した。効果による Spell のプレイでも、同じ対象・モード・価格で任意のディスカードを選べることをプレイ案の列挙について証明した。 Unit トークンの Accelerate では、費用を払えるときに登場前の選択が開くことと、Add の計画中にも支払わずに登場させる選択が残ることを証明した。Unit と Gear の宣言では追加コストを任意の組み合わせで選ぶ候補が作られ、Battlefield の追加費用を選んだ場合も同じ候補が作られる。直接プレイする Spell が Deflect を別に払うとき、支払える領域 Power と虹 Power の配分が列挙されることを証明した。すべての効果・コスト・誘発を通した証明は残っている | L4 | M4 |
| I19 | **ループの検出の健全性**: 検出器が強制的なループを報告したら、その後も強制的な答えだけで、同値な状態に戻り続ける。[LoopDetect.lean](../Riftbound/Tournament/LoopDetect.lean) で状態が完全に一致する場合を証明した。強制手と遷移を保存する任意の同値関係で、同値な状態に戻るサイクルを繰り返せると証明した。[OrderedReferences.lean](../Riftbound/Tournament/OrderedReferences.lean) では、ゾーン上の識別子の順序を保つ対応を、オブジェクトの追加・削除・移動にあわせて更新できると証明した。 また、識別子の順位は0から始まる連番になり、全ゾーンを順位で表した結果の一致と、ゾーン内の順序も保つ識別子の対応があることは同値だと証明した。 対応する識別子を同じゾーンの位置へ追加・削除・移動すると、操作後も順位で表したゾーンは一致する。有限個の参照は順序どおりに0から連番にでき、順序を保つ付け替えでは各参照が同じ順位になる。 同時死亡の記録を含むターン中の印は、対象とタイムスタンプを付け替えても、同じ種類の印を確認する結果が一致する。Combat の割り当ては対象の支配者と割り当て優先順位が対応すれば、Unit の識別子を付け替えても強制手が対応する。Predict は先頭の候補を残すか Recycle するかを選べるため強制手にならない。 保留中の参照や timestamp を含む盤面全体の付け替えについて、強制手と遷移を保存する一般証明は残っている（[tournament-model.md §5](tournament-model.md#5-ループtr-505)） | L3 | M9 |

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
- **証明**: `applyCast_targets`（Chain の Spell は、選んだ対象を持つ）、`castable_targets_present`（Spell の対象は合法なゾーンにある）、`resolveFrames_slots`（解決は、持った対象を slot にして効果を走らせる）、`mem_legalPlays`（列挙は、カード・支払い・対象の合法な組だけ）、`runEffect_safe`。**不変条件**は引き続き証明済み。
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

### M8 の実装の記録（2026-11-23）: 呪文を、タダでプレイする

- **エンジン**: `Prim.play` が、呪文を選んだとき、`playSpellStep` を使う。呪文は、新しいオブジェクトとして、チェーンに乗り、すぐに、解決し（効果を行い）、墓地へ行く。「プレイした」が記録され（Legion、「呪文をプレイしたとき」の誘発が働く）、プレイしたプレイヤーのコントロールになる。
- **近似として残したこと**: 選ぶ対象のある呪文は、プレイしない（対象を選ぶ手段が、解決のときには、まだ無い）。チェーンは開かず、相手は、答えられない。追加コスト（`paid`）と Repeat は、働かない。`cantPlay` は、見ない。プレイすると、カードの ID が変わるので、そのあとの効果は、プレイしたカードを、古い ID では、指せない（「そのあとリサイクルする」は、できない）。
- **レビューで直したこと**: 別のチェーンの項目の解決中に、タダでプレイすると、チェーンが開き直って、外側の項目が、2 回解決する恐れがあった。呪文を、`finishSpell` の代わりに、効果のあと、持ち主の墓地へ送り（`bin`）、クリーンアップを行う形にした。タダのプレイは、`paid` を、偽にする（`GameState.freeMark`。ユニットとギアの `playFree` も同じ）。
- **カードの数**: 動くカードは、298 枚のまま（Origins に、呪文をタダでプレイするカードは、Kai'Sa だけで、Kai'Sa は、Power を払うので、従来の `castInline` のまま）。他の弾のための、土台。

### M8a の実装の記録（2026-11-23）: Spiritforged 1 — Quick-Draw、Weaponmaster、Repeat、Unique

- **目標**: 「Spiritforged の 222 枚がすべて動く」（`CardDef.runs`）。始めは 34 枚。
- **Quick-Draw**: 場に出たとき、自分のユニットを 1 体選んで、付ける（`printedKeywordAbilities` の誘発型能力）。ユニットがいなければ、付かない。
- **Weaponmaster**: 場に出たとき、自分の Equipment を 1 つ選んで（付いていてもよい）、その Equip コストから Power 1 つを引いた分を払って、自分に付けてもよい（新しい `Prim.attachPaying`、`applyAttachPaying`。払えなければ付かない）。
- **Repeat、Unique**: エンジンはすでに動いていた（追加コスト、デッキの枚数制限）。`Keyword.runs` に足した。
- **近似として残したこと**: Quick-Draw のギア（と、Reaction を持つユニット）を、Chain に項目がある間に応答としてプレイすることは、まだできない（Origins の Shen と同じ）。Weaponmaster のコストは、Equip コストの Power を先頭から 1 つ引く。
- **レビューで直したこと**: Weaponmaster の誘発が解決するとき、ユニットが場に無ければ、付けも払いもしない。支払いは、Equipment を元にする（`.own` が Equipment のドメインになる）。CR の番号（Quick-Draw 819、Weaponmaster 821）を直した。テストを足した（断る、複数の Equipment、Power が `.any` の Equip、場に無いユニット、複数の友軍ユニットへの Quick-Draw）。
- **カードの数**: 動く Spiritforged は 34 枚から 46 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 2 — 今の IR で書ける 29 枚

- **書いたカード**: SFD-001、003、004、005、007、012、017、023、027、032、035、038、040、043、047、053、062、071、072、076、089、091、094、096、100、104、106、114、182。どれも、今の IR と解釈器だけで書けた（新しい仕組みは無い）。Token の定義に、名前と同じタグを足した（Mech、Sand Soldier などを「味方の Mech」と指せるように）。
- **近似**: Janna（SFD-053）は、Reaction でプレイして、Battlefield に出るカードだが、Reaction のプレイが無いので、Base に出る（「ここ」は Base になる。Base にいる味方の回復と、Base にいる敵の移動は行うが、意味は薄い）。Detonate（SFD-005）の「その持ち主」は、「味方のギアなら自分、敵のギアなら相手」で表した（2 人戦で正しい。対象が解決の前に消えたら、誰も引かない）。Dunebreaker（SFD-027）は、「手札が 2 枚以下」を、プレイするときの手札（自分を含む）で数えて、3 枚以下とした（他のゾーンからプレイすると 1 枚多く許す）。Blood Rush（SFD-003）の期間（データに「this turn」が無い）は、同じ型の Cleave に合わせて、このターン。
- **レビューで直したこと**: Dunebreaker は、自分自身を手札に数えていた（境界のテストを足した）。Detonate は、対象が解決の前に消えると、相手が 2 枚引いていた。Bushwhack の「ユニットは ready で入る」が、トークンに効かなかった（`GameState.tokenReady`）。足りなかったテスト（Repeat を払う場合、別の Battlefield、Battering Ram の下限、Yordle Explorer の境界、敵の Mech だけの Production Surge など）を足した。
- **近似（レビュー）**: Show of Strength と Rumble: 「Mighty」の判定が、パッシブの Might 増加を読まない（Gust と同じ）。Piercing Light の 2 つ目の対象と、Emperor's Divide のユニットの選択は、解決のときに選ぶので、Deflect の追加支払いと「選んだとき」の誘発が、働かない。Dropboarder の「ギアが 2 つ以上」は、解決のときに数える。
- **カードの数**: 動く Spiritforged は 46 枚から 75 枚。テストは `RiftboundTest/SpiritforgedA.lean`。

### M8a の実装の記録（2026-11-23）: Spiritforged 3 — 「戦闘に勝つ」、Gold、装備品、Battlefield

- **戦闘に勝つ**: 戦闘の終わりに、その Battlefield に残る Unit が 1 人のプレイヤーのものだけなら、そのプレイヤーが勝つ（新しい `Event.combatWon`、`TriggerEvent.winCombat`）。攻撃側の Unit は、防御側が残るとき、Recall されるので、防御側が勝つ。Unit の「I win」と、Legend の「you win」は、同じ種類の誘発で、Unit は勝った側の Battlefield の Unit、Legend は勝ったプレイヤーの Legend が、それぞれ誘発する（Draven, Vanquisher、Corrupt Enforcer、Glorious Executioner）。
- **Gold**: 「Kill this, Exhaust: [Add] ...」は動いていたが、`Ability.runs` が見ていなかったので、数えていなかった（`manaPlan`）。数えるようになった。
- **測り方**: `CardDef.runs` が、装備品が与える能力（`grants`）も見る。今まで動いていたカードで、数が減るものは無かった。
- **書いたカード**: SFD-020、115、123、181、185、190、207、212、214、217、218、219、220（13 枚）。Battlefield は、プレイヤーの conquer と hold（`youConquer`、`youHold`）で誘発する。Minefield は、山札の上の 1 枚を 2 回、墓地に置く（上から 2 枚を選ぶ手段は、まだ無い）。
- **近似**: Seat of Power の「他の Battlefield」は、「あなたが支配している」を数える（「味方が支配している」は、2 人戦では同じ）。Draven, Vanquisher の Power の支払いは、解決のときの Rune Pool から行う。
- **レビューで直したこと**: Mechanized Menace の Shield が、数値を持たず、防御側の +1 Might にならなかった（数値の無い `[Assault]`・`[Shield]` は 1 として数える）。`coverage.py` が、`grants` だけのカード（装備品）を「キーワードだけ」に数えていた。ビューアが `combat_won` を表示する。足りなかったテスト（支払いのちょうどの額、トークンが exhausted、Papertree の Rune、実際の Combat の終わりのイベントで誘発する Draven）を足した。
- **カードの数**: 動く Spiritforged は 75 枚から 89 枚（うち 1 枚は Gold: 76 枚になり、さらに 13 枚）。テストは `RiftboundTest/SpiritforgedA.lean`。

### M8a の実装の記録（2026-11-23）: Spiritforged 4 — 今の IR で書ける 12 枚（Gold、手札に戻す、条件つきの Might）

- **書いたカード**: SFD-063、074、132、135、138、147、151、154、158、159、162、163。Janna（SFD-053）は、「ここ」を、`Filter.at_ .self`（同じ Battlefield か、同じ Base）で書き直した（Base でも、そこにいる味方を回復する）。
- **近似**: Bonds of Strength と Deathgrip は、同じユニットを 2 回選ぶと、何も起きない（規則では、選べない）。Guards! は、トークンを、Power を払うか払わないかで、作り分ける（作ったトークンを、あとで指せないので、ready にするかどうかを、作るときに決める）。Windsinger は、データに括弧が無い Hidden を、手書きで足した。Chemtech Cask の「相手のターン」は、Cask の持ち主のターンでないこと。Drag Under と Void Drone の、他のゾーンからプレイするときの割引は、まだ（他のゾーンから、Energy を払ってプレイする効果が、まだ無い）。
- **レビューで直したこと**: Hidden の呪文をプレイしても、「呪文をプレイしたとき」が誘発しなかった（Chemtech Cask、Lux など）。`Event.played` を出すようにした。Bonds of Strength と Deathgrip は、片方の対象が消えると、全体が飛んでいた（残った対象に効果が届く）。Pickpocket は、対象が消えても Gold が出ていた。Direwing と Blood Money の行を直した。
- **近似（レビュー）**: Pickpocket の「Energy cost no more than 1」は、コストの無いカード（Gold トークン）を含まない。Beast Below の 2 つの対象は、プレイのとき両方選べないと、誘発ごと無くなる（片方だけ選ぶことはしない）。Ramhound の +1 は、他のカードの「Might 3 以下」に読まれない（Gust と同じ）。
- **カードの数**: 動く Spiritforged は 89 枚から 101 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 5 — 今の IR で書ける 13 枚（呪文、トークン、移動）

- **書いたカード**: SFD-077、084、085、125、128、129、145、165、176、179、196、198、204。新しい仕組みは無い。
- **近似**: Jayce（SFD-084）の「このターンに、手札からギアをプレイしてもよい」は、すぐにプレイする（解決の中で、1 つ選ぶ）。Temptation（SFD-129）は、移動先が Battlefield のときだけ動く（Base にいるユニットの場所は、指せない）。Switcheroo（SFD-145）は、同じ Battlefield にいる 2 体を、プレイのときに選ぶ。Arise!（SFD-198）の「そのうち 2 体を ready にする」は、持っている exhausted の Sand Soldier から 2 体（作った分と、前からいる分を、区別しない）。Rocket Barrage（SFD-077）の「choose one」は、解決のときに選ぶ。Glasc Mixologist（SFD-165）の「コストが Rrainbow 以下」は、Power のコストが 1 つ以下、とした。Overzealous Fan（SFD-128）の攻撃側の選択は、誘発のときに行う。
- **レビューで直したこと**: Jayce は、手札のギアの Power を払わずにプレイしていた（`playPaying` に直した。Energy だけを無視する）。Temptation は、移動先が Base にいるユニットのとき、何も起きなかった（その Base へ移る）。Arise! は、ギアの数が 2 つ未満でも、2 体を ready にしていた（作った数までにした）。Defiant Dance の対象が片方消えたとき、残りに効果が届く。足りなかったテストを足した（Jayce の Power、Switcheroo の弱い方と同じ Might、Fae Porter が Base にいるとき、Defiant Dance が終わること）。
- **近似（レビュー）**: Switcheroo、Temptation、Defiant Dance は、対象の選びが緩い（同じ Battlefield、別のユニット、という条件を、選ぶときに見られない。違反する組を選ぶと、何も起きない）。Fae Porter は、払ってから動かすので、動かせる味方がいないと、Power だけが失われる（断れる）。誤植の「Rrainbow」は、「rainbow の Power」のこと。
- **カードの数**: 動く Spiritforged は 101 枚から 114 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 6 — 「選んだとき」、Detach、トークンの判定

- **選んだとき**: `TriggerEvent.chosen`。プレイヤーが、自分のユニットを、自分の呪文で選んだとき（プレイするときの対象）に、そのユニットの誘発（Jae Medarda、Irelia, Fervent）と、「味方のユニットを選んだとき」を見張るもの（Spirit Wheel、Blade Dancer の Legend）が働く。見張る側の効果は、選ばれたユニットを `.slot 0` で指す。能力（起動型・誘発型）で選ぶ場合は、まだ働かない。
- **Detach**: `Prim.detach`（装備品を外す）。Filter に、`attachedTo`（あるものに付いている）、`isAttached`（何かに付いている）、`attached`（装備品が付いている）、`token`（トークン）を足した。トークンの判定で、Renata Glasc（Industrialist）の「トークンは ready で入る」を、`tokenReady`（パッシブの `entersReady` と、効果のあるターンの `unitsReady`）として実装した。
- **書いたカード**: SFD-011、057、107、142、144、171、177、195、221（9 枚）。
- **近似**: 「選んだとき」は、呪文のプレイ時の対象だけ（誘発する能力の対象、解決のときの選択、能力の対象は、働かない）。Irelia, Fervent の「choose or ready」の choose は、呪文だけ。Blade Dancer は、Legend を exhaust する費用を、解決のときに払う。Veiled Temple の「ready a friendly gear」の対象は、誘発のときに選ぶ。Azir, Sovereign の「any number of your token units」は、1 体ずつ「しますか」と聞く。
- **レビューで直したこと**: Angle Shot の detach が、「その unit から」に限られず、別の unit に付いた Equipment も外していた。Strike Down が外す Equipment の controller を、味方に限っていた（どちらの Equipment でもよい）。足りなかったテストを足した（Blade Dancer の敵・断る・Power なし、Renata の相手・Gold・unit カード、Veiled Temple の Equipment でないギアと相手のギア、Azir の複数の token と相手の token）。
- **近似（レビュー）**: Angle Shot の「same controller」は、選ぶときに見られない（違う組を選ぶと、何も起きず、Draw もしない）。Strike Down の damage は、呪文が与えるものとして数える（Bonus Damage が乗る）。`tokenReady` は、`entersReady` の対象が「味方のトークン」の形のときだけ読む（他の形は、無視する）。「選んだとき」は、効果から唱える呪文（`castInline`、`Prim.play`）の対象では、出ない。Azir は、すでにその Battlefield にいる token にも「しますか」と聞く（何も起きない）。
- **カードの数**: 動く Spiritforged は 114 枚から 123 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 7 — コストを減らしてプレイする、山札の上を見る

- **コストを減らしてプレイする**: `Prim.playReduced s less to`。ユニットかギアを、コストから Energy を `less` 引いて（Power はそのまま）払ってプレイする。`to` があれば、その Battlefield へ。払えなければ、何も払わず、プレイしない。手札、山札、墓地のどこからでも選べる（Void Rush、Rek'Sai, Swarm Queen、Void Burrower、Here to Help、Rumble, Hotheaded）。呪文は、プレイしない（`playReduced` は、ユニットとギアだけ）。
- **山札の上を見る**: 「top N cards を見て、1 枚を引き、残りをリサイクルする」を、`Selector.one .friendly .inMainDeck [.top N]` の選択（解決のとき、プレイヤーが選ぶ）、`returnToHand`、`recycle` と、数を束縛した `repeatN` で書いた（Called Shot、Apprentice Smith、Ornn, Blacksmith、Ravenbloom Conservatory）。「見る」は、プレイヤーが選ぶ、ということで表した（公開は、相手に見せる、という違いだけ）。
- **書いたカード**: SFD-026、041、058、111、122、140、170、187、188、215（10 枚）。Fizz は、Kai'Sa と同じ `castInline`（対象を選ばない呪文だけ。Power は払い、チェーンは使わない）。
- **近似**: Rek'Sai, Swarm Queen は、プレイしたユニットを、Base に出す（「here に出してもよい」は、まだ）。Void Rush は、見たカードのうち、呪文は、プレイしない（引く）。Here to Help は、コントロールしている Battlefield を、プレイするときの対象にするので、無いと唱えられない。Apprentice Smith と Ravenbloom は、見たカードを、引く・リサイクルするとき、プレイヤーに選ばせる形で、同じカードを選ぶ。Ornn, Blacksmith の「見たカードのうち、残り」は、枚数（4 − 引いた枚数）で数える。引く（`returnToHand`）は、「引く」の誘発を、起こさない。
- **レビューで直したこと**: `playReduced` が、印刷コストから引いていたので、Legion などのコスト軽減と重ならなかった（`effCost` から引く）。Rumble, Hotheaded は、選んだユニットが解決のときにいないと、リサイクルしないで、Mech を出せた（いるときだけ行う）。足りなかったテストを足した（Power の支払い、払えないとき、Energy が 0 に止まること、Rek'Sai の支払い、Called Shot で戻らなかったカードが底へ行くこと、Void Rush の呪文、Rumble の対象が消えたとき）。
- **近似（レビュー）**: 山札の上から見たカードを、リサイクルする順は、プレイヤーが選べない（上から順に底へ）。Rumble の「another friendly unit」を、誘発のときに選ぶ。`playReduced` で Accelerate は払えない（ユニットは exhausted で入る）。Battlefield へ出す（`to`）のは、ユニットだけ（ギアに使うと、Battlefield に置かれる）。
- **カードの数**: 動く Spiritforged は 123 枚から 133 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 8 — 費用を解決のときに払う能力、Legend の能力

- **書いたカード**: SFD-019、036、046、050、081、088、160、167、183、193（10 枚）。新しい仕組みは無い。
- **費用を、解決のときに払う**: 「Recycle a unit from your trash」（Assembly Rig）、「Kill this」（Poro Snax）、「kill a friendly gear as an additional cost」（Zaun Punk）のように、能力の費用の `AbilityCost` にまだ無いものは、能力の効果の中で行う（Energy と Power と exhaust は、これまでどおり、使うときに払う）。費用の払えない能力は、能力の条件（`ifThen` の条件。`guardOk`）に書いておくと、使えない（Assembly Rig は、墓地にユニットが無いと、使えず、Energy も無くならない）。
- **使う条件**: 「Use my abilities only while I'm at a battlefield」（Renata Glasc, Mastermind）は、効果の条件に書くと、条件が偽の間は、使えない（`guardOk`）。
- **近似**: Azir, Ascendant の「attach one of its Equipment to me」は、1 つずつ「付けますか」と聞く（複数付けられる）。Purifier の「Your Equipment each give [Assault]」は、Equipment が付いたユニットに Assault 1（Equipment 1 つにつき 1 ではない）。Card Sharp の「for each opponent who did」は、相手の Gold の数が増えたかで決める。Zaun Punk は、追加コストを、解決のときの、Kill に直した（コストを払う前にゲームが進まないので、同じ）。
- **レビューで直したこと**: Unsung Hero は、死んだあとの墓地のカードの Might を読んでいたので、実際には、いつも「Mighty でなかった」になっていた（死ぬときに、Mighty だったことを記録する: `TurnEffect.mightyUnitDied`、`noteDeath`）。Azir, Ascendant は、場を離れても、入れ替えていた（場にいるときだけ）。Lonely Poro と Unsung Hero のテストを、実際の死（`killObj`）で書き直した。足りなかったテストを足した（Assembly Rig の空の墓地、Zaun Punk の敵のギアだけ、Azir が自分を選べないこと、Grandmaster at Arms が敵の Equipment を動かせないこと）。
- **近似（レビュー）**: Lonely Poro の「alone」は、能力が解決するときに数える（同時に死んだ味方は、いなかったことになる）。Zaun Punk の追加コストは、解決のときに払うので、払う前に、相手が応答できる。Card Sharp は、相手が 2 人以上いても、Gold は 1 枚（今は 1 対 1 だけ）。
- **カードの数**: 動く Spiritforged は 133 枚から 143 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 9 — 打ち消し、キーワードの数値、コストの軽減

- **キーワードの数値**: `Amount.kwAmount s k`（「my [Assault]」）。`GameState.kwAmount` を `Combat.lean` から `Passive.lean` に移した。数値の無い `[Assault]` と `[Shield]` は 1 として数える。
- **選んだものが、自分のユニットかギアを選ぶ呪文**: `Filter.choosesMine`（Not So Fast）。
- **書いたカード**: SFD-028、045、093、103、136、164、206（7 枚）。Jaull-Fish は、既存のコスト軽減（`costMinus` に、Mighty なユニットの数）。Hard Bargain は、相手が「払う」か「打ち消される」かを選ぶ形（`eachPlayer .eachOpponent` の `eitherOf`）。Riposte は、打ち消す前に、呪文の Energy コストを読む。Dauntless Vanguard は、手札から、自分の Energy 4 と Power 1 を払って、敵のいる Battlefield に出る能力（Champion の能力と同じ形で、軽減は掛からない）。
- **近似**: Hard Bargain の「its controller」は、相手とした（1 対 1 では、自分の呪文を打ち消す場合だけ違う）。Drag Under の「他のゾーンからプレイするとき、Energy が 2 安い」は、書いていない（他のゾーンから、Energy を払ってプレイする手段は、ユニットとギアの `playReduced` だけ）。Not So Fast は、呪文だけ（能力は打ち消せない）。Lucian の Assault は、付与されたものも数える。
- **レビューで直したこと**: Hard Bargain は、Repeat を払うと、1 回目で打ち消したあとも、相手にもう一度「払いますか」と聞いていた（打ち消す呪文が Chain にあるときだけ、行う）。対象を、敵の呪文に絞った。Dauntless Vanguard のコストを、カードの印刷コストから取る。足りなかったテスト（Hard Bargain の Repeat と対象が消えた場合、Not So Fast が打ち消すこと、Jaull-Fish が 0 で止まること、Drag Under が味方も殺せること、Lucian が基地の敵と別の Battlefield に当たらないこと）を足した。
- **近似（レビュー）**: Hard Bargain の支払いは、Rune Pool にあるものだけ（相手が、Chain の上の呪文を見て、先に Energy を浮かせていないと、必ず打ち消される）。Not So Fast の「choose」は、プレイするときの対象だけ（解決のときの選択は、含まない）。Mighty の判定は、パッシブの Might 増加を読まない（Jaull-Fish）。Dauntless Vanguard の能力は、Chain に載るので、相手が応答できる（普通のプレイは、載らない）。
- **カードの数**: 動く Spiritforged は 143 枚から 150 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 10 — 1 ターンに 1 回の誘発、Legend を選ぶ、いろいろな誘発

- **書いたカード**: SFD-039、044、075、079、113、121、137、148、210（9 枚）。
- **新しい仕組み**: `Place.inLegendZone`（Legend を選ぶ。`ready`・`exhaust` が、盤面の外のゾーンから選べる）、`Filter.fromBattlefield`（直前の移動が、Battlefield からだった）、`TriggerEvent.useGearAbility`（ギアの起動型能力を使った。Prize of Progress）、`Condition.inCombat`（戦闘中）。
- **「そのターンの最初の 1 回」**: 誘発を `perTurn 1` にする（Lucian, Merciless の conquer、Draven, Audacious の戦闘に勝つ）。
- **近似**: Legion Quartermaster の「追加コストとして、ギアを手札に戻す」は、プレイしたときの誘発にした（ギアが無くても、プレイできる）。Bard, Mercurial の「追加コストとして Legend を exhaust する」は、プレイしたときに、してもよい、とした（払わないと、ユニットは動かない）。Draven, Audacious の「choose an opponent」は、1 対 1 なので、相手。`Condition.inCombat` は、戦闘中なら、どの Battlefield でも真。
- **レビューで直したこと**: Draven, Audacious の「戦闘で死んだとき」は、「戦闘中」の条件を、効果の中に置いていたので、戦闘ダメージの Cleanup で死んだときには、効果が解決するときには、戦闘が終わっていて、一度も働かなかった（条件を誘発の側に置く。実際の戦闘で、テストを足した）。Prize of Progress が、手札のギアの Hide や、伏せたギアのプレイでも、働いた（場にあるギアの能力だけ）。
- **近似（レビュー）**: Prize of Progress は、Gold などの Add 能力（Chain を通らず、`Event.activated` を出さない）を数えない。Harpoon Squad は、効果で Base へ移されるとき（`sendHome`、移動の出来事が出ない）に働かない。`perTurn` の記録は、手札に戻して出し直しても、残る（新しいカードでも、同じターンの 2 回目は、働かない）。`Condition.inCombat` は、どの Battlefield の戦闘でも真（別の戦闘の最中に、Base で死んだ場合も、真になる）。
- **カードの数**: 動く Spiritforged は 150 枚から 159 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 11 — 装備品が与える能力

- **装備品の `grants` に書ける、パッシブの変更**: `bonusDamage`（付けたユニットのプレイヤーの呪文と能力のダメージが増える: Rabadon's Deathcrown。ユニット自身のパッシブでも働く）、`keywordHere`（付けたユニットと同じ場所の、味方のユニットに、キーワード: Shurelya's Requiem）、`gainsTag`（付けたユニットに、タグ: Experimental Hexplate）、`mightIfFresh`（今のターンに付けたとき、Might が増える: Brutalizer。装備品の `attachedTurn`）、`holdIsConquer`（付けたユニットの、hold の効果は、conquer の効果でもあり、逆もそう: Skyfall of Areion）。ユニット自身のパッシブに、`doubleEquip`（付いている装備品の Might ボーナスが 2 倍: Gearhead）。
- **書いたカード**: SFD-030、042、068、073、191、192（6 枚）。
- **近似**: Skyfall の入れ替えは、conquer と hold の誘発だけ（得点は、その種類のまま）。Shurelya の「ここ」は、付けたユニットと、同じ Battlefield（または、同じ Base のユニット）で数える。Hexplate の Mech は、タグの判定にだけ効く（キーワードの判定には、効かない）。
- **レビューで直したこと**: `passiveBonus` が、`.bonusDamage` の量を、定数（`.const`）しか読まなかった（`runs` が通る式は、すべて読む）。`keywordHere` が、場にいるユニット以外にも付いて見えた（場にいるユニットだけ）。足りなかったテストを足した（Annie, Fiery と Rabadon の合計、Gearhead が Brutalizer の追加を 2 倍にしないこと、Brutalizer を付け替えるとき、Shurelya が敵を ready にしないこと、Hexplate が敵のユニットに付いたとき、Skyfall が Battlefield の conquer を hold で起こさないこと）。**OGS-001 Annie, Fiery の「Bonus Damage」が、この PR から働く**（`bonusDamage` の読み手ができたため）。
- **近似（レビュー）**: 新しい `StaticMod` は、どこに書くかで読まれる場所が決まっている（装備品の `grants` だけ: `gainsTag`・`keywordHere`・`holdIsConquer`・`mightIfFresh`、ユニット自身の `abilities` だけ: `doubleEquip`）。取り違えると、`runs` は通るが、働かない。すでに付いている装備品を、同じユニットに付け直すと、そのターンの追加は、もう一度付く。`gainedTags` と `equipKws` は、評価のたびに、場の全体を数える（遅い）。
- **カードの数**: 動く Spiritforged は 159 枚から 165 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 12 — 装備が付いたとき、バフを使ったとき、2 倍にする

- **新しい仕組み**: `Event.attached`・`TriggerEvent.attachedTo`（装備品がユニットに付いた。付いたユニットの誘発。Jax, Unrelenting）、`Event.buffSpent`・`TriggerEvent.spendBuff`（プレイヤーが、自分のユニットのバフを使った。Fae Dragon）、`Prim.double`（ターンの終わりまで、Might が 2 倍。Fiora, Peerless）、`Prim.topdeck`（山札の上に置く。Altar of Memories）、`StaticMod.noCombatDamage`（戦闘ダメージを与えない。Ezreal, Dashing）。
- **書いたカード**: SFD-082、101、110、119、169、200（6 枚）。Arcane Shift は、「banish して、持ち主がプレイする」を、そのユニットを、もう一度プレイする（Base に出し直し、「プレイしたとき」が働く）で表した。
- **近似**: Fiora, Peerless の「this combat」は、このターンの終わりまで。「one on one」は、自分の側 1 体と、相手の側 1 体。Fae Dragon の「up to four」は、1 体ずつ「しますか」と聞く（4 回）。Altar of Memories の、カードを置く先（上か底）は、プレイヤーが選ぶ。Arcane Shift は、盤上のユニットを、もう一度プレイする（Base の、exhausted で出る。バフ・ダメージ・その場の変更は、消える）。付いていた装備品は、付いたまま残る。トークンも、出し直せる。持ち主以外が唱えると、そのユニットは、唱えた人の側になる。
- **レビューで直したこと**: バフが無いユニットのバフを「使った」ことにして、`buffSpent` が出ていた（バフがあるときだけ出す）。Arcane Shift の近似の記述が、実装と逆だった。足りなかったテスト（Fiora のバフと味方、Jax が実際の Equip で引くこと、バフ込みの Ezreal のダメージ）を足した。
- **近似（レビュー）**: Altar of Memories の「底に置く」は、リサイクル（「リサイクルしたとき」の誘発が、働く）。Fae Dragon の「バフを使ったとき」は、バフを使われたユニットの、プレイヤーについて働く。Fiora の Might は、戦闘のあとも残る（同じターンの 2 回目に、上乗せされる）。
- **カードの数**: 動く Spiritforged は 165 枚から 171 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 13 — 得点の禁止、特別な Equip

- **得点の禁止**: `StaticMod.cantPlayer ps .score where_ untilTurn` を読む（`GameState.cantScoreHere`、`Passive.lean`）。`where_` は `.here`（その Battlefield）か `.anywhere`、`untilTurn` は「そのプレイヤーの N ターン目より前だけ」（0 は、いつでも）。得点の禁止された Battlefield も、Score はされる（「Score 済み」の記録が付き、`Event.scored` が出て、conquer / hold の能力は誘発する。支配も移る）が、点だけが入らない（`scoreBf` と `hold`）。Final Point の「全部の Battlefield を Score 済み」には、禁止された Battlefield も数える。『N 回目のターン』は、そのプレイヤーの通常のターンを数える（追加ターンは、数えない）。
- **書いたカード**: SFD-060（Tianna Crownguard）、150（Last Rites）、178（Blade of the Ruined King）、139（Edge of Night）と、209（Forgotten Monument。すでに書いてあって、動くようになった）。
- **特別な Equip**: 「[Equip] — Rchaos, Recycle 2 cards from your trash」「[Equip] — Rorder, Kill a friendly unit」は、キーワードの引数が無いので、自動の Equip 能力が付かない。手書きの能力（Power を払って、ユニットを選ぶ。Recycle や Kill は、解決のとき、行う）で書いた。足りないとき（墓地が 2 枚未満、他のユニットがいない）は、使えない（`guardOk`）。Edge of Night の「その場所の」は、「味方のユニット」で、場所は見ない。
- **近似**: Edge of Night の対象の選択は、手札から普通にプレイしても聞かれる（Hidden から出たときだけ、付く）。Tianna は、Battlefield の得点だけを止める（効果による得点は、止めない）。Blade of the Ruined King で殺すユニットは、装備するユニット以外から、プレイヤーが選ぶ。
- **カードの数**: 動く Spiritforged は 171 枚から 176 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 14 — 選べない、守るとき、モードの選択

- **選べない**: `StaticMod.cant .self .beChosen`（パッシブ、いつでも）を読む（`GameState.blocksChoice`、`Select.lean`）。他のプレイヤーの呪文と能力は、そのユニットを対象に選べない（`Choice.candidates`）し、解決のときの選択（`pickCandidates`）にも出ない。自分のプレイヤーは、選べる。Deflect とは別（Deflect は、払えば選べる）。
- **守るとき**: `TriggerEvent.youDefend` は、そのプレイヤーが Battlefield で守る戦闘が始まったとき、そのプレイヤーの、そこにいないユニットで誘発する（能力の最初のスロットは、その Battlefield）。
- **書いたカード**: SFD-105（Ruin Runner）、126（Loyal Pup）、049（Aphelios, Exalted。装備品を付けたとき、「このターンまだ選ばれていない」モードを選ぶ。モードの記録は、ユニットに付く `modeUsed`）。
- **近似**: 選べない（`blocksChoice`）は、カードに印刷されたパッシブだけを読む（装備品や他のカードが付けた能力は、読まない）。`youDefend` は、戦闘が始まるとき（`combatStarted`）に出る。守る側にユニットがいない Showdown では、誘発しない。Loyal Pup は、Showdown には間に合わず、戦闘ダメージだけに加わる。`youDefend` の誘発の条件（`condition`）は、Battlefield（スロット 0）を読めない（今のカードは、条件を使わない）。Aphelios は、すでに選んだモードをもう一度選ぶと、何も起きない（選べない、ではない）。Loyal Pup は、すでに Battlefield にいるときも、誘発する（動かない）。
- **カードの数**: 動く Spiritforged は 176 枚から 179 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 15 — 遊ぶ場所と費用の変更

- **遊ぶ場所**: `StaticMod.playToBf fs`（そのユニットは、手札から、条件に合う Battlefield に遊べる。能力として、`CardDef.ownBfPlay` が足す。速さは、Reaction のキーワードがあれば Reaction）と、`StaticMod.noPlayToBase`（手札から Base には遊べない。`playable` が断る）。条件は、`Filter.scoredByMine`（自分がこのターン Score した Battlefield）と `Filter.attackedByMine`（自分が攻撃している Battlefield）。`cantPlayer .. .play .here`（Rockfall Path）は、`cantActHere`（`cantScoreHere` の一般化）で読み、そこへ遊ぶ効果は Base へ遊ぶ（`playToOrBase`）。`noMoveToBaseAny`（Minotaur Reckoner）は、どこでも、ユニットが Base へ動けない。
- **費用の変更**: `StaticMod.costPlus`（敵の呪文は 1 高い。`GameState.costRaise`）を読む。`Filter.inHandZone`（手札にあるカード）で、「手札以外から遊ぶなら 2 安い」（Void Drone）を書く。
- **書いたカード**: SFD-014（Minotaur Reckoner）、015（Perched Grimwyrm）、025（Rengar, Pouncing）、146（Vex, Cheerless）、216（Rockfall Path）、010（Void Drone）。
- **近似（レビュー）**: ユニットを遊ぶ能力（Rengar、Grimwyrm、Champion Zone、空いた Battlefield）は、印刷の費用を払い、減額は読まない。遊ぶ効果（`playFree`、`playReduced`）は、Base へも遊べる（Grimwyrm の「Battlefield にだけ」は、手札からの遊びだけが守る）。Rockfall Path は、遊ぶ能力の対象に選べない（`Filter.unitsPlayable`）。費用は、先に増え（`costPlus`）、あとで減る（下限まで）。Vex は、自分が戦闘にいるときだけ働く。Rengar の Reaction は、Battlefield へ遊ぶ能力だけが Reaction の速さで、ふつうの遊びは Reaction ではない。
- **近似**: Perched Grimwyrm の「Conquer した」は、「Score した」（hold も含む）。Rockfall Path で遊べない Battlefield を選んでも、Base へ遊ぶだけで、選ぶのを止めない。Vex の費用の変更は、Energy だけを動かす（Power の「虹」は動かさない。最小は Energy 1）。Rengar は、Reaction だが、Chain に呼応して遊ぶことはできない（既存の近似と同じ）。Void Drone を遊ぶ Champion Zone などの能力は、印刷の費用を払う。
- **カードの数**: 動く Spiritforged は 179 枚から 185 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 16 — 遊んだユニットにバフ、動いたとき

- **遊んだユニットにバフ**: `TurnEffect.unitsBuffed`（Rally the Troops）。そのターンに、そのプレイヤーが遊ぶユニットは、バフを持って出る（`PlayMark.buff`。手札からの遊びと、無料の遊びの両方）。トークンを作る効果は、バフしない（近似）。バフは、`buffed` のイベントを出さない（「バフされたとき」は、働かない）。トークンを作る効果は、`played` を出さないので、Forecaster にも働かない。
- **書いたカード**: SFD-166（Rally the Troops）、131（Ancient Warmonger。『Assault は、ここにいる敵ユニットの数』。`StaticMod.assaultCount`。Assault は戦闘のダメージだけを増やし、Might は増やさない）、065（Forecaster。味方の Mech を遊んだとき Vision。Forecaster 自身も数える）、054（Jax, Unmatched。味方の Equipment（印刷の Quick-Draw を持たないもの）を遊んだとき、味方のユニットに付ける。手札にある間の Quick-Draw の代わり。手札以外から遊んだときも付ける。Reaction の速さは、無い）、112（Kato the Arm。動いたとき、Deflect と自分の Might を、味方のユニットに、このターンだけ与える。Kato が持つ印刷のキーワード Deflect だけを写す近似）。
- **カードの数**: 動く Spiritforged は 185 枚から 190 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 17 — Mighty になったとき、好きな量を払う Add

- **Mighty になったとき**: `TriggerEvent.becomeMighty` は、バフ（`Event.buffed`）か、装備品を付けた（`Event.attached`）ことで、Might が 5 未満から 5 以上になったときに誘発する（`GameState.becameMightyTriggers`: 増えた Might を引いて、5 未満になるかを見る）。永続でない Might の付与（`grant`）、Mighty のまま出てくること、パッシブで Might が増えることは、読まない（近似）。
- **好きな量を払う**: `payAny`（1 つずつ「払ってもよい」を最大 12 回聞き、払った数を `notes .unitPaid` で読む）。Hextech Anomaly（Power → Energy）と Ancient Henge（Energy → Power）は、Reaction の能力（Chain に載る）で、「Add は応答できない」は、守らない。
- **書いたカード**: SFD-180（Fiora, Worthy）、205（Grand Duelist）、083（Hextech Anomaly）、117（Ancient Henge）、189（Fire Below the Mountain）。
- **近似（レビュー）**: 増えた Might は、付ける前後の `equipBonus` / `buffBonus` の差で測る（`buffDelta`、`attachDelta`）。同じ一歩に、バフと装備品が両方あると、2 回誘発しうる。`buffsExtraMight` を後から足して Might が増えても、誘発しない。好きな量を払う Add（Gear）を、同じターンに 2 回使うと、1 回目に払った分が、2 回目の数に残る（`unitPaid` の記録は、ターンごと）。
- **近似**: Fire Below the Mountain の Add は、「Gear を遊ぶか、Gear の能力を使うときだけ」の制限がない（制限つきの Add は、解釈されない）。
- **カードの数**: 動く Spiritforged は 190 枚から 195 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 18 — 数える量、ダメージの防止

- **数える量**: `Amount.excess`（そのプレイヤーが、このターン最後の戦闘で割り当てた余りのダメージ）、`Amount.heldPoints`（このターン、hold で点を取った Battlefield の数。`Object.held` は、hold だけが付け、ターンの始めに消える）、`Amount.gearsPlayed`（このターン、遊んだ Gear の数）。
- **ダメージの防止**: `TurnEffect.damagePrevented`（ユニットに付く）。そのターンの、そのユニットへの最初のダメージ（0 でないもの）は、防がれ、記録は消える（`GameState.shielded`、`useShield`、`dealObj`）。戦闘のダメージも、`dealObj` を通る。
- **Battlefield の費用の変更**: Battlefield のパッシブは、それを支配しているプレイヤーのために働く（`GameState.sourceOwner`。だれも支配していなければ、働かない）。
- **書いたカード**: SFD-055（Needlessly Large Yordle。hold の点 1 つにつき Energy を 2 安く。**Power の Calm を安くする部分は、読まない**）、120（Sivir, Ambitious）、194（Counter Strike）、213（Ornn's Forge。最初の Token でない Gear は 1 安い）。
- **近似（レビュー）**: `heldPoints` は、hold した Battlefield の数で、得点が禁止された Battlefield も数える。余りのダメージの記録は、「このターン最後の戦闘」で、戦闘のない conquer（空の Battlefield への移動）では古い値が残る（Sivir は、その量で撃つ）。Battlefield のパッシブの『支配しているプレイヤー』は、費用の変更だけが読み、他の変更（`entersReady` など）は、まだ所有者で読む。Counter Strike は、ダメージを防がれない（`noDamage`）ユニットには、盾を使わない。
- **近似**: Needlessly Large Yordle の費用は、Power の Calm の減額を動かさない（高くなる側）。Counter Strike は Reaction だが、Chain に呼応して遊ぶことは、既存の近似と同じ。Ornn's Forge の「最初」は、このターンに遊んだ Gear の数が 0 のとき（Token の Gear は、遊んだ数に入らない）。
- **カードの数**: 動く Spiritforged は 195 枚から 199 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 19 — ターンの終わりに戻る、空いた Battlefield

- **ターンの終わりに戻る**: `TurnEffect.endTrigger card idx`（対象のオブジェクトに付ける）は、ターンの終わりに、そのカードの `idx` 番目の能力を、そのオブジェクトを source にして誘発させる（`GameState.fxTriggers`。カードの識別子は、データとして持つ。エンジンは、カード名を知らない）。`Prim.returnControl` は、持ち主の支配に戻す。
- **空いた Battlefield**: `endShowdown` は、だれも支配していない Battlefield を conquer したとき、`TurnEffect.openConquest` を、その Battlefield に記録する。`Condition.openConquered`（自分のいる Battlefield に、その記録がある）で読む。
- **書いたカード**: SFD-202（Hostile Takeover。Battlefield の敵ユニットの支配を得て、ready にする。戦闘の始まりと conquer は、Cleanup の通常の流れ。ターンの終わりに、持ち主へ戻して、recall する）、116（Yone, Blademaster）。
- **近似**: ユニットの支配を得る（`takeControl`）と、そのユニットのいる Battlefield は、新しい支配者に Contested にされる（ほかの敵ユニットがいれば戦闘になる）。`openConquest` は、Cleanup で支配者が消えた Battlefield にも付く（守備側を全滅させた conquer でも、Yone は誘発する）。ターンの終わりの誘発は、Ending フェーズの始まりに一度だけ集める（そのあとに遊んだ Hostile Takeover は、戻らない）。Yone のダメージは、対象を選ばず、解決時に選ぶ。Hostile Takeover で、相手が先にそのユニットを動かした・殺したときは、何も起きない。ターンの終わりの誘発は、そのターンの最後のフェーズの開始（`phaseStarted .. .ending`）に出る。
- **カードの数**: 動く Spiritforged は 199 枚から 201 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 20 — 死ぬ代わりに、Rune のリサイクル、使った Power

- **死ぬ代わりに**: `GameState.deathSaver`（Guardian Angel: 付けたユニットが死ぬなら、代わりにその Equipment が死ぬ。Soraka: 同じ Battlefield の、Might の小さい味方が死ぬなら、代わりに）。助けられたユニットは、ダメージが消え、exhausted になり、base に戻る（`saveUnit`）。**読む場所は、致命的なダメージを与える瞬間（`dealObj`）と、`kill`（`killOrSave`）**。Cleanup の致命的なダメージの判定（Might が下がって死ぬ場合など）と、Temporary の死は、読まない（近似）。
- **Rune のリサイクル**: Rune が Rune Deck へ動くと（`Event.moved`）、`TriggerEvent.recycleRune` が、そのプレイヤーの物と Legend に誘発する。
- **使った Power**: `RunePool.spent`（Rune Pool が空になるまでに払った Power の数。Main の始まりと Ending で、Pool と一緒に消える）、`Amount.powerSpent`。
- **書いたカード**: SFD-051（Guardian Angel）、173（Soraka, Wanderer）、024（Rell, Magnetic。無料で遊んだ Equipment を付ける。このターンに遊んで、まだ付いていない Equipment は、みな付く）、143（Sivir, Mercenary）、203（Battle Mistress）。
- **近似（レビュー）**: Soraka の「ここ」は、Battlefield だけ（Base にいる Soraka は、救わない）。救ったとき、`damaged` のイベントは出さない。Deflect の支払いは、`spent` に数えない。Rell は、費用（Power も）を払わず遊ぶ（`play`）。『ダメージを受けたら死ぬ』の効果（`killOnDamage`）も、救う。
- **近似**: Rell は、その手前に遊んだ付いていない Equipment（このターンに遊んだもの）も、付ける。Sivir の『2 つ以上の虹』は、Power を 2 つ以上払ったこと（`spent`）。
- **カードの数**: 動く Spiritforged は 201 枚から 206 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 21 — 手札に頼らない能力、ターン限りの能力、遊ぶときの追加の費用

- **Battlefield の能力**: Battlefield の起動能力は、それを支配しているプレイヤーが使う（`activatable`）。Battlefield のパッシブは、その支配者のために働く（費用の変更、Add の追加）。`Condition.legendReady`（手札でなく、自分の Legend が ready）。
- **ターン限りの能力**: `TurnEffect.grantsAbility card idx`（そのターン、ユニットが、カードの誘発能力を持つ。Relentless Pursuit）。
- **Add の追加**: `StaticMod.manaExtraEnergy`（Add する物が、Energy を、さらに生む。Chem-Baroness の Gold）。
- **遊ぶときの追加の費用**: 追加の費用（Accelerate、Repeat、カード自身の追加の費用）は、その時の状態で決まる（`GameState.extrasFor`）。`StaticMod.extraCostLess`（Ezreal: 追加の費用が 1 安い）、`repeatCostLess`（Marai Spire: Repeat が 1 安い）、`TurnEffect.nextSpellRepeat`（Temporal Portal: 次の呪文は、自分の費用で Repeat）。費用は、Energy から先に減り、次に Power が減る（`Cost.less`）。`playable`、`castable`、`legalPlays` と、I8 の不変条件は、この状態つきの費用を使う。
- **書いたカード**: SFD-208（Forge of the Fluft。Battlefield の能力で、自分の Legend を exhaust して、Equipment を付ける）、197（Emperor of the Sands）、080（Bellows Breath）、184（Relentless Pursuit）、199（Prodigal Explorer）、201（Chem-Baroness）、211（Marai Spire）、078（Temporal Portal）、149（Ezreal, Prodigy）。
- **近似（レビュー）**: Marai Spire の「1 安い」は、Energy だけを減らす（Power だけの Repeat は、安くならない）。Ezreal が追加の費用を 0 にすると、それは、必ず払ったことになる（`paidExtra`）。付与された誘発能力（Relentless Pursuit）は、解決のとき、ユニット自身の `used` の同じ番号の使用を数える（ユニットの、同じ番号の `perTurn` の能力と、数が衝突する）。`spellsChoseEnemy` は、なくなった対象（死んだユニットなど）を、敵とみなす（敵を殺す呪文を数えるため）。自分のユニットを選んで、そのユニットが消えると、誤って数える。Temporal Portal は、2 回使っても、Repeat は、1 つだけ。Battlefield の Add（`manaReady`）は、まだ所有者で読む。
- **近似**: Forge of the Fluft は、Legend の能力ではなく、Battlefield の能力（Legend を exhaust する）。Emperor of the Sands の『Sand Soldier は Weaponmaster を持つ』は、後で書いた（Spiritforged 23）。「Equipment を遊んだ」は、「Gear を遊んだ」で読む。Bellows Breath の 2 つ目と 3 つ目は、ダメージを受けていないユニットから選ぶ（同じユニットに 2 回は撃たない代わりに、ダメージの残っているユニットを選べない）。Relentless Pursuit は、Equipment を付ける部分と、Move の行き先に Base を選ぶ以外の細かい点（移動先は、Battlefield か Base）を、書いていない（Equipment を付けない）。Prodigal Explorer は、呪文だけを数える（ユニットの能力は、数えない）。Ezreal の「1 安い」は、Energy から減らす。追加の費用を 0 まで安くすると、払ったことにならない。
- **カードの数**: 動く Spiritforged は 206 枚から 215 枚。

### M8a の実装の記録（2026-11-23）: Spiritforged 22 — 山札から公開、テキストの複製、死ぬときの追放（222 枚）

- **山札から公開**: `Prim.reveal` は、山札のカードを公開すると、`Event.revealed` を出す。`TriggerEvent.revealedFromDeck` は、そのカード自身に誘発する（Undertitan: 2 Energy を Add する）。
- **テキストの複製**: `StaticMod.copiesUnitText`（Equipment）。付いたユニットは、自分のカードの誘発能力を、もう一度持つ（Svellsongur）。
- **死ぬときの追放**: `StaticMod.banishOnDeath`（Equipment の grants）。付いたユニットは、死ぬと、Trash でなく、Banishment に行く（The Zero Drive の Deathknell）。`killObj` の行き先が、これで決まる。
- **書いたカード**: SFD-175（Undertitan）、059（Svellsongur）、090（The Zero Drive）、109（Akshan, Mischievous）、018（Void Hatchling）、029（Rek'Sai, Breacher）、141（Irelia, Graceful）。
- **後で書いた近似**: SFD-018 Void Hatchling は、山札のカードが公開されたあと（`Event.revealed`）、一番上を見て、リサイクルしてもよい（公開の『前』ではなく、『後』）。SFD-029 Rek'Sai は、手札以外から遊んだ味方のユニットが、1 Energy と 1 Fury を払って ready になれる（`Object.playedFromHand`、`Filter.playedFromElsewhere`）。SFD-141 Irelia は、自分の呪文が自分を選んだとき、1 Energy を戻す（`.chosen` の誘発。『1 Energy か 1 Power』のうち Energy だけ。払ったあとの戻しなので、先に全額を払える必要がある）。
- **山札から公開の限界**: `Event.revealed` を出すのは、`Prim.reveal`（OGN-008 と OGN-200）だけ。Main Deck の上を公開すると書かれた、ほかのカード（Apprentice Smith など）は、`reveal` を使わず `top` で書いてあるので、イベントを出さない（Undertitan の Add と Void Hatchling は、そこでは働かない）。
- **追放の限界**: ユニットが死んで追放されると、`loc`（いた場所）が消える（`moveObj`）。いた場所を読む死ぬときの誘発（Kog'Maw, Caustic など）は、The Zero Drive が付いていると、働かない。死んだ瞬間に Banishment へ行くので、Trash を読む能力（Immortal Phoenix、Chosen Champion を戻す）も働かない。Svellsongur の複製は、死ぬときの誘発（死ぬと、新しい物になって Equipment が外れる）と、見ている能力には、効かない。Akshan の『もし払ったなら』は、誘発の条件でなく、解決時に読む。
- **この 7 枚のうち、書けていなかった文**（最初は `status := .drafted` だけで、動く数には入ったが、この文は動かなかった。018、029、141 は、上の近似を後で書いた）:
  - SFD-018 Void Hatchling: 「公開するときは、先に一番上を見て、リサイクルしてもよい」。公開の置き換えは、まだ無い。
  - SFD-029 Rek'Sai: 「手札以外から遊ぶユニットは、Accelerate を持つ」。Accelerate は、手札から遊ぶときだけで、手札以外から遊ぶ効果（`playReduced`）は、費用の外の Accelerate を読まない。
  - SFD-141 Irelia: 「自分の呪文で自分を選ぶものは 1 安い」。費用が、選んだ対象に依る形は、まだ無い。
  - SFD-090 The Zero Drive: （後で書いた。下の『Spiritforged 23』）
  - SFD-059 Svellsongur: ユニットの、誘発する能力だけを、複製する（起動する能力、パッシブは、複製しない）。
  - SFD-109 Akshan: （後で書いた。下の『Spiritforged 23』）
- **カードの数**: 動く Spiritforged は 215 枚から 222 枚（全部）。

### M8a の実装の記録（2026-11-23）: Spiritforged 23 — 近似を、本物にした分

- **トークンのプレイ**: 作ったユニットのトークンは、`Event.tokenPlayed` を出す（`tokenPlays`）。`TriggerEvent.playToken` を待つ能力だけが見る。トークンはカードではないので、「カードを遊んだとき」を待つ能力（Viktor など）は、見ない。「ユニットを遊んだとき」を待つ能力も、トークンは、まだ見ない（近似）。
- **Emperor of the Sands**: 『Sand Soldier は Weaponmaster を持つ』を、Sand Soldier が遊ばれたときの誘発（Equipment を 1 安く付けてもよい）として書いた。
- **Akshan**: 取った Gear は、`Object.takenBy`（取った Unit のカード）を覚え、その Unit が盤面を離れる（盤面でないゾーンへ動く。`TriggerEvent.leave`、`Event.moved` から検出）と、持ち主の支配に戻り、持ち主の Base へ戻る。`Prim.takeControlUntilLeaves`。同じカードの Unit が離れるときは、その Unit が取った Gear もまとめて戻る（近似）。
- **The Zero Drive**: 付いたユニットが死んで追放されると、そのカードは `Object.banishedWith`（Equipment）を覚える。『3 Energy と Mind、これを追放: 追放したユニットを、全部、無料で遊ぶ（付いていないときだけ）』を、`Prim.playBanishedWith` で書いた。
- **レビューで直したこと**: `leave` は、盤面から出た移動だけで誘発する（`Object.leftBoard`）。ドローや捨てでは誘発しない。Akshan が返す物は、取ったときの支配者と、離れる Akshan の持ち主が同じ物だけ（相手の Akshan が取った物は、返さない）。残る近似: 取った印（`takenBy`）は、返したあとも残る。Zero Drive は、支配者の追放ゾーンだけを見る（持ち主と支配者が違うとき、遊ばれない）。
### M8a の実装の記録（2026-11-24）: Spiritforged 24 — 近似だった物を、本物にした

- **Irelia**: 選んだ対象で、費用が変わる。`GameState.chooseCut`（その呪文が選んだ、自分の `chosenSpellsCostLess` を持つ物の数）、`Cost.cutOptions`（Energy を 1 つ、または Power を 1 つ、安くした費用）、`paysForXT`、`playPaymentsOfT`。`castable`、`legalPlays`、`playMark`（追加の費用の判定）、I8 の不変条件が、これを使う。『1 Energy か 1 Power』は、遊ぶ人が、払い方で選ぶ。以前の Energy の払い戻しは、やめた。
- **Void Hatchling**: 『公開するときは、先に一番上を見て、リサイクルしてもよい』を、置き換えとして書いた。`StaticMod.lookBeforeReveal` があるとき、`Prim.reveal` は、`lookTop`、リサイクルしてもよい、`Prim.revealNow` の順に動く（`runEffect1`）。山札（Main Deck と Rune Deck）から選んだカードの公開にだけ働く（手札を公開するカードには、働かない）。山札の公開の誘発は、やめた。
- **Rek'Sai**: 手札以外から遊んだ味方のユニットは、そのユニット自身の領域の Power 1 つと 1 Energy を払って ready にできる（領域ごとに 6 つの選択肢）。
- **Svellsongur**: 付いたユニットの、パッシブ能力も、もう一度働く（`activeMods`）。
- **Prodigal Explorer**: ユニットが使った能力（起動する能力と、誘発した能力）が選んだ敵の物も、数える（`Object.chose`、`Object.noteChose`）。
- **レビューで直したこと**: Void Hatchling は、Main Deck から選んだカードの公開にだけ働く（手札や Rune Deck の公開には、働かない）。Irelia の削減は、2 枚の Irelia で、Energy と Power を 1 つずつ安くする組も数え、同じ物を 2 度選んでも 1 回だけ数え、同額の支払いを重ねない。Rek'Sai は、すでに ready なら、もう払わない。壊れていた Spiritforged のテスト（Akshan、Emperor、Zero Drive）を、元に戻した。
- **Void Hatchling（その後）**: Main Deck の上の何枚かを公開すると書かれたカード（SFD-041 Apprentice Smith、170、187、188、215、OGN-160）は、`Prim.revealTop` で公開を書き、Void Hatchling の置き換えが働く。
- **Forge of the Fluft と Svellsongur（その後）**: Forge of the Fluft は、Legend が持つ能力として書いた（すべての Legend が、『Exhaust: 自分の Equipment を、自分のユニットに付ける』という能力を持ち、自分が支配する Battlefield が `legendsAttach` を持つときだけ使える。`CardDef.legendAbilities`）。Svellsongur は、付いたユニットの、起動する能力も複製する（すべてのユニットが、自分の起動する能力の複製を持ち、複製する Equipment が付いているときだけ使える。`CardDef.copiedAbilities`）。
- **残っている近似**: Irelia の割引は、必ず掛かる（全額払いは、遊べない）。Power の割引は、先頭の記号から落とす。Energy の割引は、`effCost` の下限を見ない。AI（`riftbound-trace` の自動対戦）は、最大の支払いを選ぶので、割引を使わない。Void Hatchling は、`Prim.reveal` を使うカードだけに働く（Main Deck の上を公開する、ほかのカードは、`top` で書いてあり、公開として扱わない）。Forge of the Fluft は、Legend が持つ能力でなく、Battlefield の能力（支配者が使い、自分の Legend を exhaust する）。Sivir の『2 つ以上の虹』は、払った Power の数で読む。
- **まだ近似のもの（過去の記述。上の Spiritforged 24 で、一部は本物になった）**: SFD-018 Void Hatchling（公開のあとで見る）、SFD-029 Rek'Sai（払って ready）、SFD-141 Irelia（Energy の払い戻し）、SFD-059 Svellsongur（誘発する能力だけ）、SFD-199 Prodigal Explorer（呪文だけ数える）、SFD-208 Forge of the Fluft（Battlefield の能力）、SFD-143 Sivir（Power を数える）。

### M7 の実装の記録（2026-11-23）: 味方の Exhaust 能力を、すべて持つ（最後の 1 枚）

- **エンジン**: `Condition.hasFriendlyCard`（自分の、場にある、またはレジェンドの、その名前のカードがある）。
- **動くようになったカード**: Heimerdinger, Inventor（111。味方のレジェンド、ユニット、ギアの、Exhaust 能力を、すべて持つ）。Origins の 28 枚の、Exhaust 能力を、写して、「その名前の味方のカードがあるとき」だけ使える能力として、書く（`heimerdingerOf`）。写した能力の `self` は、Heimerdinger になる。
- **動くカード**: 297 → **298 枚（Origins の全部）**。
- **レビューで直したこと**: 条件の「かつ」「または」は、片方が、まだ答えられなくても、もう片方が決めるなら、決める（`Condition.eval`）。写した能力が、元のカードが無くても、使えてしまっていた（Baited Hook）。`docs/coverage.md` の数が、手書きの部分の、移動で、ずれていたのを、直した。
- **近似として残したこと**: 他のセット（OGS、UNL など）のカードの Exhaust 能力は、写さない。「味方のカードがある」は、カードの名前で判定する（その能力を持つ、そのカードの、条件は、読まない）。同じ名前のカードが、2 枚あっても、能力は、1 つ。

### M7 の実装の記録（2026-11-23）: 墓地の呪文を、その場で、唱える（1 枚）

- **エンジン**: `Prim.castInline`（選んだ呪文を、その場で唱える: Power を払い、呪文の効果を、すぐに行い、そのあと、カードをリサイクルする。`castInlineStep`）。`Filter.noChoices`（プレイするとき、対象を選ばない呪文）、`Filter.costBelowPoints`（エネルギーのコストが、自分の点数より小さい）。
- **動くようになったカード**: Kai'Sa, Evolutionary（112。征服したとき、墓地の、エネルギーのコストが、自分の点数より小さい呪文を、エネルギーなしで、プレイして、リサイクルしてもよい）。
- **動くカード**: 296 → **297 枚**。
- **近似として残したこと（レビュー）**: 追加コストと Repeat は、無視する（その場で、1 回、解決する）。「呪文をプレイできない」の制限（`cantPlay`）は、見ない。
- **近似として残したこと**: 対象を選ぶ呪文は、選べない（対象を、解決のときに選ぶ手段が、無い）。「呪文をプレイしたとき」の誘発は、働かない。呪文は、チェーンを使わず、すぐに、解決する。

### M7 の実装の記録（2026-11-23）: Power だけを払って、プレイする（1 枚）

- **エンジン**: `Prim.playPaying`（エネルギーのコストを無視して、プレイする。Power のコストは、プールから払い、払えなければ、プレイしない）。
- **動くようになったカード**: Promising Future（115。各プレイヤーが、山札の上 5 枚を見て、ユニットかギアを 1 つ選び、エネルギーを払わずにプレイし、残りをリサイクルする）。見る、選ぶ、プレイ、リサイクルの数え方は、Baited Hook と同じ。
- **動くカード**: 295 → **296 枚**。
- **レビューで直したこと**: `playPaying` は、ユニットかギアかを、払う前に確かめる。払えないときの、テストを足した。
- **近似として残したこと（レビュー）**: 選んだカードが払えないと、山札に残る代わりに、他の 4 枚と一緒に、リサイクルされる。プレイは、全員が見たあとではなく、プレイヤーごとに続けて行い、呪文をかけた人が先。
- **近似として残したこと**: 呪文は、選べない（プレイできない）。「次のプレイヤーから、順にプレイする」は、各プレイヤーが、自分の分を、続けて行う（プレイヤーの番号順）。

### M7 の実装の記録（2026-11-23）: 残すものを選ぶ（1 枚、エンジンの変更なし）

- **動くようになったカード**: Divine Judgment（244。各プレイヤーが、ユニット 2 つ、ギア 2 つ、ルーン 2 つ、手札 2 枚を選び、残りをリサイクルする）。「残す 2 つを選ぶ」を、「リサイクルするものを 1 つずつ選び、2 つになるまで繰り返す」で書く（`keepTwo`。数は、段階の始めに、1 回数える）。
- **動くカード**: 294 → **295 枚**。
- **レビューで直したこと**: ルーンを 3 個以上持つ場合の、リサイクル（ルーンデッキへ）を、テストする。
- **近似として残したこと（レビュー）**: 選ぶ順番は、プレイヤーの番号順で、手番のプレイヤーからではない（`eachPlayer` の既存の近似）。
- **近似として残したこと**: 選ぶ順番は、「リサイクルするもの」を選ぶ形（残すものを選ぶのと、同じ結果になる）。呪文自体は、チェーンにあるので、手札には、含まれない。

### M7 の実装の記録（2026-11-23）: 相手のカードを、自分がプレイする（1 枚）

- **エンジン**: プレイしたカードは、持ち主ではなく、プレイした人がコントロールする（`enterBase`）。`Prim.banish` が、山札などの場の外から、選んだカードを、追放できる（`understoodPickAny`）。
- **動くようになったカード**: Blind Fury（025。相手の山札の一番上のカードが、ユニットかギアなら、コストなしで、自分がプレイする。呪文なら、追放する）。1 対 1 で、「それぞれの相手」は、1 人。
- **動くカード**: 293 → **294 枚**。
- **近似として残したこと（レビュー）**: 「このターンにプレイしたカード」を数える判定（Legion、`playedOther`、`cardsPlayed`）は、持ち主で数えるので、Blind Fury でプレイした相手のカードは、自分のプレイとは、数えない。
- **近似として残したこと**: 呪文は、プレイせずに、追放だけ行う。「追放してから、プレイする」を、山札から、直接プレイする（追放のゾーンを、通らない）。

### M7 の実装の記録（2026-11-23）: 追加のターン（1 枚）

- **エンジン**: `GameState.extraTurns`（追加のターンを取るプレイヤー）と `turnShift`（追加のターンの数。ターン順は、追加のターンが無かったように、続く）。`nextTurnPlayer` が、追加のターンを先に返し、`beginTurnStep` が、使った分を、減らして、ずらす。`Prim.extraTurn` を、動かす。`SameMeta` は、この 2 つの欄を、見ない。`first_turns` の定理に、追加のターンが無いという条件を足した。
- **動くようになったカード**: Time Warp（122。この後に、追加のターンを取る。これを追放する）。
- **動くカード**: 292 → **293 枚**。
- **レビューで直したこと**: 「後手の最初のターンの Rune 3 枚」（`channelCount`）と、「これまでに取ったターンの数」（`turnsTaken`）は、追加のターンを数えない `turn - turnShift` で数える。
- **近似として残したこと（レビュー）**: Limited の「最初のドロー」（`extraDraws`）は、まだ `turn` で数え、先手の追加のターンが最初の 1 周の間に入ると、誤る。`turnsTaken` に、追加のターンは、含まれない。`Invariant/Turn.lean` の `turnPlayerAt` は、ターン順だけの定義で、`nextTurnPlayer` とは、別。
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
- **当時の近似**: Chosen Champion を Legend と同じタグを持つ最初の Unit として選んでいた。現在は [Chosen Champion の実物カードの追跡](#chosen-champion-の実物カードの追跡2026-11-27) で、登録した1枚を識別する。
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
- **当時の近似**: Fortified Position の Shield 2 はターン終了まで続き、Sanctum には残すカードの順番の選択がなかった。現在は [Origins の Battlefields](#origins-の-battlefields-2026-11-27) の実装で解消した。

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

- **エンジン**: `Place.onChain`（Chain の上のスペル。自分自身と、能力は含まない）。選ぶ対象が、盤面か Chain の上のスペルになった（`mem_candidates`・当時の `targetsOk_mem_inPlay`・`castable_targets_inPlay` の主張を、「盤面、または Chain の上のスペル」に広げた。`.slot` も同じ）。`Prim.counter`（スペルを、解決せずに、持ち主の Trash へ送る）。
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

### M8c Vendetta 1 — Burn と既存の効果 IR で書けるカード

- `Prim.burn` は CR 441 に従い、Main Deck の上から指定枚数を Trash に置く。残りが足りない場合は、置ける分を置いて Burn Out を処理し、山札を補充して残りを置く。移動には `sendObj` を使い、`burnEffect_safe` で物理カードの保存などを示した。Burn 専用の誘発は後続のカードで扱う。
- Shadow Temple、Oasis Raider、Fretful Feline、Decree of Unity、Acceleration Gate など、21 枚の効果を追加した。Vendetta の `drafted` は 167 枚中 36 枚になった。これら 5 枚は `RiftboundTest/VendettaA.lean` で、誘発条件、対象の選択、山札の残り枚数などを検査する。

### M8c Vendetta 2 — 印刷された Flow コスト

- 呪文は通常のタイミングで、Trash からは Flow の代替コストでプレイできる（CR 829）。Flow でプレイした呪文は、解決または打ち消しで Chain を離れるとき Banishment へ置く。
- Brittle Steel と Perfect Execution の効果を追加した。Brittle Steel は手札と Trash でコストが異なること、Reaction の許可が増えないこと、解決と打ち消しの両方で Banishment へ置かれることをテストした。

### M8c Vendetta 3 — Empower の状態と印刷されたマナコスト

- CR 442–443 に対応し、Unit・Gear・Legend の Empowered を記録する。盤外へ出ると状態は消え、Disempower すると 1 回分を失う。CR 827 のマナコストを持つカードは、Empowered でない間に起動できる。
- Steel Paws の既存定義が動くようになり、Rage Amplifier、Guttural Roar など 9 枚の効果を追加した。割引、マナ以外の Empower コスト、Empowered の複数回起動を許すカードは後続で扱う。

### M8c Vendetta 4 — Flow と Empower を使うカード

- Lacerate、Tomb-Raider Barbara、Ambessa 2 種など、11 枚の効果を追加した。Lacerate のテストでは Disempower の後の Might で撃破を判定することを確かめた。Shadow Assassin は自分の Trash に同名カードがあるときだけ Ready で出る。
- Vendetta の 167 枚中、58 枚が `drafted`、54 枚が `CardDef.runs` を満たす。いずれの件数も `RiftboundTest/Cards.lean` で検査する。

### M8c Vendetta 5 — Empower の起動コストと Deathknell

- Disempower を起動コストとして支払い、効果を Chain に置く前に状態を更新する。Kayle の重ね掛けと、死亡直前の Empowered を参照する Deathknell に対応した。
- Questionable Tome、Kayle、Noxian Emissary など 15 枚の効果を追加した。167 枚中 73 枚が `drafted`、69 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 6 — 起動コストの軽減と対象条件

- 起動コストの Energy 軽減を合法手の列挙と受理に反映した。Baccai Sandspinner は Rune 4 枚と 5 枚で費用が変わる。Stargazer は自分の Trash から唱える Flow 呪文にだけ適用し、最低 1 Energy を保つ。
- Platewyrm Egg、Public Execution など 10 枚の効果を追加した。167 枚中 83 枚が `drafted`、79 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 7 — 打ち消し、Deflect、Channel の制約

- Decree of Rage は打ち消しても Chain に残る。Decree of Insight と Heisho は合法性の判定と実際の支払いの両方で Deflect を無視する。Heisho の効果は、その Battlefield にいる対象に限る。
- Sandstone Chimera の Channel 枚数制限と、Sacred Protector の戦闘ダメージ条件を追加した。167 枚中 88 枚が `drafted`、84 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 8 — 移動前後の対象と再プレイ

- Akali は移動元か移動先の Battlefield の Unit を選び、Rogue Assassin は Showdown 中の Battlefield にいる味方 Unit を選ぶ。Mask Mother の捨てたときの効果も追加した。
- Temporal Breach では、追放した Unit を持ち主が元の Battlefield へプレイする。相手に支配されていた Unit も、新しいオブジェクトとして持ち主の側に戻ることをテストした。
- 167 枚中 92 枚が `drafted`、88 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 9 — 敵から選ばれない効果

- Twilight Shroud の保護はターン中だけ働き、Akali, Silent の保護は同じ Battlefield で戦闘をしている間だけ外れる。どちらも味方の選択は許す。
- 167 枚中 94 枚が `drafted`、90 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 10 — Trash のカードを対象にする

- CR 355 に従い、明示された Trash・Legend Zone・Champion Zone のカードを Chain に置く段階で選べる。解決前に対象が別のゾーンへ移ると、その対象の ObjId は無効になる。Trash にあるカードの Deflect は働かない。
- Shadows of the Past と Tail-Cloaked Matriarch に加え、Gust Monk と Ravenbloom Prefect を追加した。Gust Monk の追加コストは Assault の誘発条件であり、ユニットを Ready で出す Accelerate の支払いとは区別する。
- 167 枚中 98 枚が `drafted`、94 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 11 — Spiderling の構築ルール

- Spiderling はデッキの同名枚数制限を免除する。Core Rules と Constructed の判定で同じ規則を使い、Constructed では Main Deck とサイドボードの両方を含めて検査する。
- 同じ場所にいる自分のほかの同名 Unit の枚数だけ Might が増える。敵の同名 Unit や別の場所にいる同名 Unit は枚数に含めない。
- 167 枚中 99 枚が `drafted`、95 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 12 — 付与された Flow と複数の代替コスト

- Kennen, Storm of Shuriken はプレイ時に Burn 2 を行い、Conquer 時には自分の Trash の呪文に、そのカードの基本コストを Flow としてターン終了まで与える。
- CR 829 に従い、異なる Flow コストが複数あれば、プレイ時に使うコストを指定できる。割引後に支払いが一致しても区別し、Repeat の計算には選んだコストを使う。合法手の列挙と `Legal` の一致は `mem_legalPlays` と `legalActions_iff`、支払いの保存則は `applyCast_pays_cost` で検査する。
- Lightning Rush は見たカードのうち 1 枚を引くか見送り、残りを Trash に置く。山札が 3 枚未満の場合も、見たカードの範囲で処理する。
- 167 枚中 101 枚が `drafted`、97 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 13 — Might の閾値と盤面から読む効果

- Renekton, Brute の誘発は、すでに場にいる Unit の実効 Might が 10 未満から 10 以上になったときに発生する。効果の解決に加え、Standard Move で Battlefield のパッシブが適用された場合も検出する。閾値以上を維持している間は再誘発せず、下がってからもう一度到達すれば再誘発する。
- Morgana, Vindictive は解決時に対象に記録されているダメージと同じ量のダメージを与える。Keeper of Law は、Unit がちょうど 2 体いる Battlefield を支配している場合に 2 Energy と 1 Order Power が軽減される。
- 167 枚中 103 枚が `drafted`、100 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 14 — 起動コストとして手札を捨てる

- CR 423.3 に従い、必要な枚数をすべて選べる場合にだけ起動できる。手札から選んだカードを対象と区別し、能力を Chain に置く前に捨てる。列挙と合法性の一致を `mem_discardPayments` と `mem_legalActivates` で検査する。
- Punching Poro は任意のカード、Sky Cruiser は Gear、Mel, Defiant Soul は Spell を捨てる。Sky Cruiser の Energy と Exhaust は同時に支払い、Mel は Empower 後に Battlefield の条件を満たす敵 Unit を追放する。
- 167 枚中 106 枚が `drafted`、103 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 15 — Burn に続く誘発

- Forgotten Relic はプレイ時と自分の Beginning Phase に Burn 1 を行う。その Burn で Unit を Trash に置いたときは、Might を記録して別の誘発型能力を Chain に載せる（CR 388-389, 441）。味方 Unit を選ぶのはこの誘発の確定時で、解決前に相手が応答できる。
- 誘発が参照する Might は、最初の能力の発生源が場を離れたり、Burn したカードが Trash を離れたりしても使える。シナリオでは非 Unit、別の効果による Burn、Burn Out 後の Burn も検査する。
- 167 枚中 107 枚が `drafted`、104 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 16 — 移動後に山札の上を公開する

- Pakaa Protector が移動したら、山札の一番上を公開する。Unit なら引き、それ以外なら Trash に置き、Pakaa Protector に +2 Might を与える。山札が空なら公開も後続処理も行わない（CR 432.1.c）。
- 位置の入れ替えで Base に戻った Unit も移動として記録する。Standard Move、入れ替え、Recall、複数の型を持つ Unit をシナリオで検査する。
- 167 枚中 108 枚が `drafted`、105 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 17 — 各プレイヤーのターン数と得点の置換

- Ol' Poro は自分の第 1〜3 ターンにはプレイできない。追加ターンも数える。効果で無料または軽減されたコストでプレイする場合にも制限が働く。
- Otterpus は、得点するプレイヤー自身の第 1・2 ターンに Conquer または Hold で得る 1 点を 1 ドローに置き換える。得点済みの印は残り、Final Point の規則ですでにドローになる場合は 1 回だけ引く。
- Beginning Step の誘発と Cleanup が終わってから Scoring Step を進める（CR 315.2, 335）。Dusk Rose Lab で Otterpus を倒すかどうかによって、その後の Hold が得点かドローか変わる。Shadow Temple は得点を置き換えたドローの次のカードから Burn する。
- 167 枚中 109 枚が `drafted`、107 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 18 — 付与された Tank を Might の計算に使う

- Kinkou Temple は、その Battlefield にいる両プレイヤーの Unit のうち、Tank を持つものに +1 Might を与える。キーワードのレイヤーで Tank を確定してから Might を計算する（CR 479.3-479.4）。装備や効果で与えられた Tank にも適用する。
- 回帰テストで、Doran's Shield の装備を外したとき、Eye of Twilight が与えた Tank がターン終了時に切れたとき、別の Battlefield にいるときの Might を確認した。
- 167 枚中 110 枚が `drafted`、108 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 19 — 戦闘参加とターン中のダメージ

- 戦闘の開始時と Cleanup で参加した Unit を記録する。戦闘結果と Conquer に続く処理が済んでから戦闘を終え、途中で移動したり Recall されたりして場に残る Unit の能力も誘発させる（CR 466.2.c.3, 468.7）。
- Mournful Witness は自分が参加した戦闘の終了時に Empower される。Affectionate Poro はそのターン中にダメージを受けていなければ 1 枚引く。正のダメージを受けたターンは回復後も参照でき、無効化されたダメージは記録しない（CR 418-419）。
- Threshold of the Gray は戦闘開始時に 1 回誘発し、戦闘に参加する攻撃側と防御側に Energy を 1 ずつ与える。3 人のターン順で、防御側と次の手番のプレイヤーが異なる場合をテストした。
- 戦闘ダメージと特殊 Cleanup に伴う誘発を解決してから勝敗を判定する。特殊 Cleanup の Recall が起きた戦闘には勝敗がつかない。戦闘結果の誘発が解決した時点の盤面で Control と Conquer を判定する（CR 468.2-468.5）。
- 戦闘ダメージで倒れた Kog'Maw の Deathknell が勝敗の判定に間に合うことと、戦闘勝利時の効果で最後の Unit が移動すると Conquer が起きないことをテストした。
- 167 枚中 113 枚が `drafted`、111 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 20 — Predict で選んだ順に山札へ戻す

- Predict は山札の先頭から指定枚数までを見て、残すカードと Recycle するカードを選ぶ。残すカードは選んだ順に先頭へ戻し、2 枚以上を Recycle するときは乱数で順を決めて末尾へ送る。山札が足りない場合はある分だけを見る（CR 417.5, 437）。
- Apprentice Mage は Empower されたときに Predict 2 を行い、Empowered の間は +1 Might を得る。Clairvoyance は Predict 5 の並べ替えが済んだ山札から 2 枚引く。
- 回帰テストで、残す順序、Recycle の乱数回答、指定枚数より短い山札、先頭に戻したカードのドローを確認した。
- 167 枚中 115 枚が `drafted`、113 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 21 — 基礎 Might と死亡時の遅延誘発

- Dragon Form は指定した Unit の基礎 Might を 5 にする。バフ、装備、加減算はその基礎値に適用する。基礎 Might の変更はターンの終了時または Unit が盤面を離れると失効する。手札からのプレイと Trash からの Flow の両方を確認した（CR 143.2.a, 479.2, 479.4）。
- Ending Step の誘発を解決したあと、Expiration Step で回復、ターン効果の失効、Rune Pool の消去を行う。Blighted Battleaxe の終了時ダメージが Dragon Form の失効より先に解決することをテストした（CR 317.1-317.2）。
- Siphoning Strike は Rune が 7 枚以上なら 7 ダメージ、それ以外なら 4 ダメージを与える。対象の Unit がそのターン中に倒れたとき、呪文を使ったプレイヤーが Rune を 1 枚 Exhausted で Channel する。対象自身の Deathknell と別に誘発する（CR 391-393）。Deadly Flourish も同じ遅延誘発の処理を使う。
- 167 枚中 117 枚が `drafted`、115 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 22 — Battlefield による Power の増減

- Mystic Vortex の Showdown 中、Reaction を持つカードのプレイに Power を 1 加える。Quick-Draw、Ambush、Hidden から Reaction を得る場合にも適用する（CR 341, 356.3, 811.6, 813, 819.1.b, 822.1.b）。
- Sandswept Tomb は、そこにいる味方 Unit を選ぶ Spell の総 Power コストを Battlefield ごとに 1 減らす。複数のドメインの Power がある場合は、どの記号を減らすか選べる。Repeat や Deflect を含む支払いと、効果でコストを払ってプレイする Spell も検査した（CR 355-356, 420.3, 809）。
- Temporal Portal が付ける Repeat は Spell の印刷コストを参照する。Mystic Vortex の追加 Power を Repeat のコストにも足してしまうことを防ぐ。[Spiritforged 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/riftbound-spiritforged-faq/)
- 軽減で任意の追加コストが 0 になり、支払い額が一致する場合は、追加コストを払うかどうかを明示的に選ぶ処理が残っている。
- 167 枚中 119 枚が `drafted`、117 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 23 — Unit トークンと効果内のコスト

- Up from the Deep は Tentacle 2 体を出す。Flow でも 1 体ずつ行き先を選ぶ。Illaoi, Prophet of the Great Kraken はプレイ時と自身のいる Battlefield の Conquer・Hold 時に Tentacle を 1 体出し、自分が支配する Unit トークン 1 体につき Might が 1 増える。Tentacle は Bilgewater タグを持つ（CR 185.2.a, 187.10, 355.2, 473.2）。
- Death Mark は Burn 3 の後に Shadow Clone を出す。Zed, Without a Sound の Conquer は Shadow Clone を Base に出す。起動型能力で味方の Shadow Clone と位置を入れ替える。Shadow Clone は 0 Might で場に残り、自身が攻撃するとき、Trash の Unit を Banish して Assault 4 をそのターン中得られる（CR 142.4.b, 187.11, 359.3.e.14.b, 807）。
- Profiteer は能力を Chain に置くときに対象を選び、解決時に自分の Legend などから Empowered を 1 つ取り除いて、その対象を Empower できる。Shadow Clone の Banish と同じく、先の処理が成立したときだけ後続の指示を実行する（CR 355.10.c.1, 359.3.e.14.b, 443）。[Vendetta 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/vendetta-rules-faq-and-clarifications/)
- ビューアにトークンの行き先を Base または Battlefield の名前で表示する。
- 167 枚中 124 枚が `drafted`、122 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 24 — プレイ時に手札を捨てる追加コスト

- 追加コストを払うプレイでは、対象や Flow コストと別に、捨てる手札を指定する。プレイするカード自身は候補に入らない。Energy と Power の支払い後に捨て、相手が Reaction を選べる前に処理する。捨てたカードについても Discard の誘発を発生させる（CR 353, 355.10.c, 357.1–357.2, 423.3）。[Radiance 公式 FAQ](https://playriftbound.com/en-us/news/organizedplay/radiance-rules-faq-and-clarifications/)
- Ruthless Strike は 3 ダメージを与え、手札を捨てた場合は 5 ダメージを与える。Repeat だけを払った場合は 3 ダメージを繰り返す。Zed, From the Shadows は手札を捨ててプレイしたときに Shadow Clone を出す。
- ビューアでは対象を選んだ後に、捨てない手と捨てられるカードを表示する。効果によるプレイで物品や手札を任意の追加コストとして使う選択は別途必要。
- 167 枚中 126 枚が `drafted`、124 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 25 — 確定したプレイとパーマネントの解決

- そのターンに確定したプレイについて、プレイヤー、当時のオブジェクト ID、カードの型を保持する。パーマネントのプレイが解決した順も記録する。Hidden からのプレイは確定時に記録し、解決時に重複して数えない（CR 420.4, 811）。
- Crumbling Sands は対象と別の Spell をいずれかの対戦相手が確定していれば、対象を打ち消す。その別の Spell が先に打ち消されていた場合も数える。Swain, Visionary はそのターンに Unit、Gear、Spell を確定していた場合、Conquer 時に 1 点を得る。Patched Porobot は Unit と Gear の両方を満たす（CR 420.4.b）。[Vendetta 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/vendetta-rules-faq-and-clarifications/)
- Jayce, Brilliant Inventor は自身のプレイ時と、そのターンに自分の非トークン Gear のプレイが初めて解決したときに、自身以外の Exhausted のオブジェクトを Ready にできる。Legend も選べる。誘発を見送っても、その Gear が最初だった記録は残る（CR 355.10.a, 383.1, 383.3.a, 420.4.a）。
- Hungry Wolf は敵 Unit を対象に選んだターンに限り、Order Power を払って自身を Ready にし、ターン終了まで Might を 1 増やせる。1 ターンに 1 回。その Unit が場を離れても対象に選んだ履歴は残る（CR 355.7, 371）。
- 167 枚中 130 枚が `drafted`、128 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 26 — 起動型能力のコスト軽減

- Piltovan Forge の支配者は、そのターン最初にプレイする自分の Gear の起動型能力のコストを 1 Energy 軽減する。コストが 0 の Add や打ち消された能力も最初の 1 回として数える（CR 356.4, 357, 430.2）。
- Risen Altar の支配者は、その戦場にいる自分の Unit の Empower コストから 1 Energy または任意の 1 Power を軽減できる（CR 190.6.d, 356.4.c, 827）。
- 167 枚中 132 枚が `drafted`、130 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 27 — Banish の実行者とダメージの発生元

- Master of Shadows は、支配者が所有するカードを自分で Banish したときに Empower される。Flow の Spell は打ち消されても Banish される。Disempower と Exhaust を起動時に支払い、解決時に手札を 1 枚捨ててから 1 枚引く（CR 383, 428, 829.1.b.1）。[Vendetta 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/vendetta-rules-faq-and-clarifications/)
- Esteemed Hierophant は支配者が Rune を 7 枚以上持つ間、敵の Spell と能力からのダメージを防ぐ。味方の効果と Combat Damage は通常どおり受ける（CR 142, 438）。
- 同じ Unit に複数の Banish 置換が重なる場合は、先に作られた置換を適用する。支配者による適用順の選択は未実装（CR 372）。
- 167 枚中 134 枚が `drafted`、132 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 28 — 上限のない対象選択と合計 Might

- Corrupted Dragon は勝利まで 4 点以上なら Ready で出る。攻撃時に同じ戦場にいる Might 5 以下の敵 Unit を任意の数だけ対象にし、解決時も条件を満たす対象を Base に移動する（CR 355.13, 359.3.e.2）。
- 対象を 0 体にして能力を確定する選択と、能力を見送る選択は、M8c Vendetta 30 で区別した（CR 355.13, 383.3.a）。
- Decree of Discord は敵の Order Unit を合計 Might 5 まで選び、手札に戻す。解決時に合計が上限を超えたら、追加できる対象をすべて含む組み合わせから選ぶ。対象は確定時に選んだ Unit に限り、組み合わせの決定で対象指定の誘発は再発生しない（CR 355.11, 359.3.e.2）。
- 別の効果で Repeat が付いた場合は、実行ごとの対象の組み合わせを確定時に選ぶ処理が残る（CR 820.2）。
- 167 枚中 136 枚が `drafted`、134 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 29 — 支配者ごとの選択と敵の効果

- Cataclysmic Duel は、解決時にターンプレイヤーから順に各プレイヤーが自分の Unit を 1 体選び、その後で残りを Kill する。Unit がいないプレイヤーの選択は飛ばす。これらの選択は対象指定の誘発を起こさない（CR 303.2.a, 355.10.e）。
- Jagged Cutlass は Body Power 1 で Equip し、装備先を敵の Spell や能力による移動から守る。味方の移動効果、Standard Move、Recall は引き続き行える（CR 358.3.a, 447, 451, 456）。
- Decree of Focus は、敵の Fury Unit と戦闘しているか敵の Fury Spell に指定されている味方 Unit に、そのターン中 Might を 4 与える。解決時にも対象の条件を確認する（CR 355.9.b, 359.3.e.2）。
- ビューアは各プレイヤーが自分のカードを選ぶ場面と、解決時に対象を絞る場面を区別して案内する。
- 167 枚中 139 枚が `drafted`、137 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 30 — 誘発型能力を確定するときの費用

- Bottled Constellation は、自分の Main Phase の開始時に、ほかの味方 Unit と Gear から計 3 枚を選んで Kill できる。これらはコストの選択なので対象指定の誘発を起こさない。能力を解決したときに 1 点を得る（CR 355.10.c, 357.2.a, 383.3.a, 383.3.b）。
- Kennen, Keeper of Balance は、プレイして出たときと攻撃したときに、Energy 2 を払うと Unit を対象に取る。Stun は解決時に行う。同じ場所に Stun された敵 Unit がいる間は Might が 2 上がる（CR 383.3.a, 383.3.b, 424）。
- 見送った能力は Chain に載らず、対象を 0 体選んで確定した Corrupted Dragon の能力には応答できる。費用は確定時に支払い、打ち消されても戻らない（CR 355.13, 383.3.a, 383.3.b, 426.1.c）。
- 現状は Pool と Basic Rune で誘発コストの Energy を支払える。確定中に任意の Add 能力を起動する選択と、Rune から Deflect の Power を捻出する選択は残っている（CR 357.1.a, 809）。
- 167 枚中 141 枚が `drafted`、139 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 31 — 移動の効果

- Twilight Step は Might 3 以下の Unit を対象に取り、その Unit の Base または別の Battlefield へ移動する。行き先を選ぶ時点は Vendetta 33 で確定時に修正した（CR 355.4, 421, 451, 829）。
- Shuriken Flip は味方 Unit を必ず対象に取り、Battlefield にいる敵 Unit を 1 体まで追加で対象に取る。敵にダメージを与えてから味方を移動する。敵の対象を省いた場合や失った場合も、有効な味方の対象は移動できる（CR 355.13, 355.18, 359.3.e）。
- Shadow Dash は自分の Unit がいる Battlefield に敵 Unit を移動し、そこに自分の Unit がちょうど 2 体いれば、その 2 体にターン終了まで Might を 1 ずつ与える。移動前の場所や、第三者が入れない戦場は候補から除く（CR 359.3.e.14, 449.2.a, 451.2, 464）。
- 移動先を選んでも対象指定の誘発は起きない（CR 355.4, 355.6）。
- 167 枚中 144 枚が `drafted`、142 枚が `CardDef.runs` の検査を通る。

### M8c Vendetta 32 — Tank の優先順と有限のダメージ軽減

- Dune Surfer の支配者は、同じ Battlefield で戦闘ダメージを割り振るときに Tank の優先順を無視する。相手側の割り振りや、カードが持つキーワード自体はそのまま扱う（CR 467.2.c.2, 815）。
- Ki Barrier はそのターン中の受けるダメージを合計 7 まで軽減する。残量は次のダメージに持ち越し、場に留まる移動でも維持する。戦闘では残量を含めて致死ダメージに必要な割り振り量を計算する（CR 438.2, 438.3, 438.5, 467.2.c.5）。
- 戦闘で Ki Barrier と Lotus Trap が重なる場合は、影響を受ける Unit の支配者が軽減と倍増の適用順を選ぶ。戦闘外のダメージで複数の置換が重なったときの選択と、複数の軽減・倍増を交互に適用する選択は未実装（CR 372, 467.2.c.5）。[Vendetta 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/vendetta-rules-faq-and-clarifications/)
- 167 枚中 144 枚が `drafted`。転記済みの 144 枚すべてが `CardDef.runs` の検査を通る。

### M8c Vendetta 33 — 呪文を確定するときのモードと移動先

- Sanction と Mesmerize は、呪文を確定するときにモードとそのモードの対象を選ぶ。選択は応答中も保持する。Sanction は対象の Empowered をターン終了時に切り替える遅延誘発を作る（CR 355.3, 355.5, 390-393, 442, 443）。
- Twilight Step、Shuriken Flip、Shadow Dash の移動先は、通常プレイでも Flow でも、相手が応答する前に選ぶ。有効な対象の効果だけを解決する。Shadow Dash で選んだ Battlefield から味方 Unit がいなくなっても、別の Battlefield は選び直さない（CR 355.4, 358.3.a, 359.3.e, 451.1）。
- ビューアは、モード名または移動先と、対象を選択前に表示する。
- Repeat を別の効果で得た場合に、追加実行ごとのモードや移動先を確定時に選ぶ処理が残っている（CR 820.2）。
- 167 枚中 146 枚が `drafted`。転記済みの 146 枚が `CardDef.runs` を通る。

### M8c Vendetta 34 — 誘発型能力を確定するときのモード

- Jayce, Hammer in Hand は Ready したとき、Assault 2・Deflect 2・Ganking のうち 1 つを選んでから Chain に載る。解決時にそのキーワードをターン終了まで得る（CR 355.3, 383.3）。
- Minah Swiftfoot は Battlefield に移動したとき、全員が 1 枚捨てるか、全員が 1 枚引くかを選ぶ。解決時はターンプレイヤーから手番順に実行する（CR 303.2.a, 355.3, 383.3）。
- ビューアに、誘発型能力を確定するときに選べるモード名を表示する。
- 167 枚中 148 枚が `drafted`。転記済みの 148 枚が `CardDef.runs` を通り、19 枚が未転記。

### M8c Vendetta 35 — 誘発型能力の Burn コストと Hidden

- Shadow Order Disciple は移動時に、山札の一番上のカードを Burn して能力を確定するか、見送るかを選べる。Burn は応答前に支払い、能力が打ち消されても支払いは戻らない。山札が空なら見送りだけが可能（CR 383.3.a, 383.3.b, 441.3, 441.4）。
- Tornado Warrior は伏せた状態からプレイしたときに、その場所のオブジェクトを選んで能力を確定できる。解決時も対象がその場所にいれば Empower し、ターン終了時に Disempower する。移動で対象が不正になった場合は両方の指示を実行しない（CR 199.1, 355.5, 359.3.e, 359.3.f, 383.3.a, 390-393, 442, 443）。
- 167 枚中 150 枚が `drafted`。転記済みの 150 枚が `CardDef.runs` を通り、17 枚が未転記。

### M8c Vendetta 36 — 誘発型能力でプレイヤーを対象にする

- Blade Twirler は各ターンの最初の移動で誘発する。自分も含めて 1 人を対象に選び、相手が応答する前に確定する。解決時には選んだプレイヤーだけが Burn 1 する（CR 355.7, 355.15, 383.3, 441）。
- 対象プレイヤーの選択をオブジェクトの対象枠と別に保持し、ビューアにプレイヤーの席番号を表示する。
- 167 枚中 151 枚が `drafted`。転記済みの 151 枚が `CardDef.runs` を通り、16 枚が未転記。

### M8c Vendetta 37 — 最初に解決したカードと、次のカードの軽減

- Astral Heron は、そのターンに初めてカードのプレイが解決した時点で Battlefield にいれば誘発する。誘発の解決後にプレイする次のカードの総コストを Energy 2 と Power 2 軽減する（CR 356.4, 420.4, 420.5）。
- 通常プレイ、Flow、Hidden、効果によるプレイが、次のカードとして軽減を使う。無料でプレイしたカードや、確定後に打ち消されたカードも軽減を使う。Deflect は軽減前の総 Power に含める（CR 356.2.a.2, 356.4.d, 811, 829）。
- 軽減後の支払額が一致する任意の追加コストを、支払いと別に選ぶ処理が残っている。
- 167 枚中 152 枚が `drafted`。転記済みの 152 枚が `CardDef.runs` を通り、15 枚が未転記。

### M8c Vendetta 38 — 呪文の追加コストを選んで確定する

- Rampage は印刷された Body Power の追加コストを払うか見送るかを確定時に選ぶ。軽減後の総額が同じでも選択を分け、支払いの記録は呪文の支配者が変わっても保持する（CR 135.2.b.7, 355.1, 356.4.f.1）。
- 追加コストを選んだ場合だけ味方 Unit に +2 Might を与える。その後、2体が互いに現在の Might に等しいダメージを与える。ダメージの発生源は Unit として扱う（CR 359.3.e, 418.6.b.3）。
- 呪文の印刷された追加コストと Repeat の回数を別々に記録し、両方の選択をビューアに表示する。Unit や Gear の一部では、同額の任意コストを個別に選ぶ処理が残る。
- 167 枚中 153 枚が `drafted`。転記済みの 153 枚が `CardDef.runs` を通り、14 枚が未転記。

### M8c Vendetta 39 — 対象を選ぶ効果と Might の置換

- Empowered の Mel がいる間、そのプレイヤーが支配する呪文と能力は打ち消せない。選ばれた Unit の Might 減少量は 1 増え、元の効果の下限も適用する。Moonfall は移動させる Unit を確定時に最大 1 体選んで Deflect を払い、解決時に移動するか決める（CR 355.5, 355.12, 370, 426, 809）。
- Empowered の Gangplank が選ばれた場合、Stun、Might 減少、手札に戻す処理をターン終了時までの +3 Might に置き換える。Switcheroo では Gangplank 側の減少だけを置き換え、もう一方の増加量を保つ（CR 370）。[Vendetta 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/vendetta-rules-faq-and-clarifications/)
- 167 枚中 155 枚が `drafted`。転記済みの 155 枚が `CardDef.runs` を通り、12 枚が未転記。

### M8c Vendetta 40 — 選んだ相手の Trash からプレイする

- Kharox の Empower で誘発する能力は、相手を 1 人選んで確定する。解決時にその相手が Burn 3 し、その後、今 Burn されたカードも含め、その相手の Trash から Unit を 1 枚選んで費用を無視してプレイできる。元の所有者は維持し、能力のプレイヤーが支配する（CR 127, 355.7, 420, 441）。
- 167 枚中 156 枚が `drafted`。転記済みの 156 枚が `CardDef.runs` を通り、11 枚が未転記。

### M8c Vendetta 41 — 呪文が相手を選び、その手札を公開する

- Decree of Strength は相手を 1 人選んで確定し、相手が応答できる。解決時にその相手は現在の手札をすべて公開する。術者は公開された Mind カードを 1 枚選び、相手がそれを自分の Main Deck の下に置く（CR 355.7, 355.10.a, 417, 425.3.a）。
- 呪文のプレイヤー対象をオブジェクト対象や支払いと別に記録する。ビューアで対象の席番号、公開されたカード、選べる手札を確認できる。
- 167 枚中 157 枚が `drafted`。転記済みの 157 枚が `CardDef.runs` を通り、10 枚が未転記。

### M8c Vendetta 42 — 山札で見たカードを軽減してプレイする

- Wild Claw は Main Deck の上から最大 5 枚を記録し、Banish 後にプレイできる Unit または Gear だけを候補にする。追加コストを選んだ後で総 Energy を 5 軽減し、必要な Power と行き先を確定する（CR 355-357, 356.4.f, 420.3, 432.1.c）。
- 選んだカードを Banish してプレイし、残りをランダムな順で Main Deck の下に置く。その後、場に出たカードを Empower するか選ぶ（CR 417.5, 442）。
- 必要な基本 Rune の操作は、効果による既存の支払い処理で補う。プレイの確定中に起動する Add 能力を個別に選ぶ操作が残る。
- 167 枚中 158 枚が `drafted`。転記済みの 158 枚が `CardDef.runs` を通り、9 枚が未転記。

### M8c Vendetta 43 — 解決中に呪文の名前を指定する

- Fallen Feline の誘発が解決するときに、フォーマットで使える呪文を論理カード ID で指定する。指定は公開され、カードのコピーがゲーム内にあるかどうかに依存しない（CR 759-762）。
- Fallen Feline が Battlefield にいる間、相手は指定された呪文をプレイできない。Chain にすでに置かれた呪文は解決できる。Base に戻ると制限が解除され、場を離れて別のオブジェクトになると指定を失う（CR 054, 124）。
- 通常の Unit をプレイする際に、自分が支配する Battlefield を選べる。Perched Grimwyrm のようにプレイ先を指定するカードには、固有の制限を適用する（CR 355.2）。
- 167 枚中 159 枚が `drafted`。転記済みの 159 枚が `CardDef.runs` を通り、8 枚が未転記。

### M8c Vendetta 44 — 解決時の Might とターン中の起動型能力

- Dominus は確定時に Unit を対象にし、解決時にも適切な対象か確認する。その時点の Might と同じ値をターン終了まで加える。Might が負なら増加量は 0（CR 355.11, 359.3.e.2, 433.1, 479.4.c）。
- 対象 Unit はターン終了まで、無指定の Power を 2 つ払って自身を Ready にする起動型能力を得る。Unit の支配者が通常の速度で起動し、費用の支払い後に相手は応答できる。Chain に載った能力の定義は、付与の失効後も参照できる（CR 317.2, 337, 376-381, 479.3）。
- 167 枚中 160 枚が `drafted`。転記済みの 160 枚が `CardDef.runs` を通り、7 枚が未転記。

### M8c Vendetta 45 — 起動型能力でプレイヤーを選び、Gear を渡す

- Glowstone は Power 2 で Empower できる。Disempower と Exhaust を支払う起動型能力では、確定時に自分を含むプレイヤーを 1 人対象にする。解決時にそのプレイヤーへ支配権が移り、その Base に Recall する。所有者と Exhausted 状態は保たれる（CR 355.7, 357, 456-460, 739-743）。
- 現在の支配者の Ending Step に誘発し、Glowstone を Kill した後、その能力の支配者の Unit すべてに 5 ダメージを与える。誘発後に Glowstone が場を離れた場合も、ダメージは解決する（CR 317.1, 337）。
- Ending Step の Chain で Reaction をプレイする処理は、既存の Main Phase 制限の見直しが必要（CR 312.2.c-d, 813.1.c）。
- 167 枚中 161 枚が `drafted`。転記済みの 161 枚が `CardDef.runs` を通り、6 枚が未転記。

### M8c Vendetta 46 — 基礎 Energy と Legend の Exhaust

- Curator of the Sands は、プレイヤー自身が基礎 Energy 7 以上の Unit・Gear・起動型能力をプレイすると誘発する。カードは印刷・コピーされたコスト、能力は選んだ基礎コストを参照する。軽減や追加コストは判定に含めない（CR 204.1.b, 206-206.1）。
- 誘発を確定するとき、Rune を最大 2 枚指定し、Curator 自身を Exhaust する。見送る選択や 0 枚を指定する選択があり、すでに Exhausted なら支払えない。解決時には残っている合法な対象を Ready にする（CR 355.7, 355.11, 383.3, 415.4, 416）。
- 167 枚中 162 枚が `drafted`。転記済みの 162 枚が `CardDef.runs` を通り、5 枚が未転記。

### M8c Vendetta 47 — Battlefield の配置許可と制限

- Battlefield への通常プレイと、Here to Help のように配置先を指定する軽減プレイで、プレイ制限を共通に検査する（CR 054.2, 355.17.b）。Perched Grimwyrm は、Arachnoid Horror が配置を許可していても、そのターンに Conquer した Battlefield にしか出せない。効果が禁止された場所を指定した場合は、その Unit のコストを支払わない。
- Dragon Roost の任意コストと、Temporal Breach などの効果と配置先が競合した場合の選択を、続けて実装する（CR 355.17.a）。[Vendetta 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/vendetta-rules-faq-and-clarifications/)

### M8c Vendetta 48 — Dragon Roost の任意コスト

- 通常プレイでは、Dragon Roost の支配者にかかわらず、Dragon のプレイヤーが任意で Power 2 を払ってそこにプレイできる。複数の Roost に払う場合は、そのうちどこに出すかを選ぶ。Perched Grimwyrm 自身の配置制限と Mageseeker Warden の制限を適用する（CR 054.2, 355.1, 355.17）。
- Battlefield の追加コストと Unit 自身の追加コストを別々に確定する。軽減後の支払額が同じでも、支払うと決めたコストを記録し、Accelerate を選んだときに Unit が Ready で入る（CR 356.4, 805）。
- Dragon Roost は `partial`。Temporal Breach や Here to Help からのプレイにも追加コストの選択を出し、効果から受けた配置指定と競合する場合を扱う必要がある。167 枚中 162 枚が `drafted` で `CardDef.runs` を通り、4 枚が `todo`。

### M8c Vendetta 49 — 効果で Dragon をプレイする場合の配置先

- 効果による Unit のプレイでも、Roost の追加コストを選べる。必須の配置指定が複数あるときは、同時に満たせる指定をまとめ、互いに両立しない組み合わせからプレイヤーが選ぶ。Unit 自身や場の効果による配置制限を先に適用する（CR 355.16–355.17, 420.3）。
- Temporal Breach で元が Base の Elder Dragon を再プレイする場合、所有者は追加コストを見送って Base に戻すか、支払って Base または Roost に出せる。Here to Help は解決中に Unit と配置先を決める。手札から使い、支配する Roost に払ったときは Roost に出す。Hidden から使った場合は Hidden の場所の指定も加わる（CR 811.1.d.5）。[Vendetta 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/vendetta-rules-faq-and-clarifications/)
- 167 枚中 163 枚が `drafted` で `CardDef.runs` を通り、4 枚が `todo`。

### M8c Vendetta 50 — Unit 用の Energy

- Butcher of the Sands は、任意のドメインの Power 2 と自身の Exhaust を払い、Chain を使わず Unit 用 Energy 2 を加える。Reaction の Add は Ending Step の Chain でも優先権を渡さず解決する（CR 357.1, 430.2–430.3）。
- Unit 用 Energy は Unit のプレイとその起動型能力の支払いに使う。Spell、Gear、Hide、能力の解決中に単独で要求される支払いには通常の Energy が必要になる。混在時は使える Unit 用 Energy から先に消費し、Main Phase 開始時とターン終了時に Rune Pool とともに消える（CR 166–167, 445, 811.1.c）。
- 167 枚中 164 枚が `drafted` で `CardDef.runs` を通り、3 枚が `todo`。

### M8c Vendetta 51 — Trash からの通常プレイ

- Endless Riches をプレイすると、その誘発能力が手札と Trash を追放してから Burn 7 を行う。場にある間はコントローラーの Draw Phase を省き、効果によるドローは通常どおり行う（CR 315.4, 428, 441）。
- コントローラーは Trash の Unit・Gear・Spell を通常コストでプレイできる。Flow を持つ Spell は Flow コストも選べる。Chain に入れた時点で Flow の使用を記録する（CR 356, 420.1, 829.1）。
- Main Deck 以外からコントローラーの Trash に入るカードは追放する。Spell が解決したときは、その時点の効果を適用する。Thermo Beam のように複数の Gear を同時に破壊する場合は、同時に場を離れる Endless Riches の置換も適用する（CR 052, 367–370, 428）。
- 167 枚中 165 枚が `drafted` で `CardDef.runs` を通り、2 枚が `todo`。

### M8c Vendetta 52 — Equipment の装着中に Unit をコピーする

- Shady Spectacles の装着で誘発する能力は、コピー効果を適用する前に判定する。その後、Equipment のコントローラーが装着先とは別の味方 Unit を選ぶ（CR 370.1.b.1, 435, 725.1）。[Vendetta 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/vendetta-rules-faq-and-clarifications/)
- コピー元の印刷・コピー済みの特性を記録し、装着先の状態と物理カードを保持する。複数のコピーは適用順に重なり、装着が解けると下のコピーか元の特性に戻る。付け直すと起動回数とモードの選択履歴は新しい能力で数え直す。場を離れる直前のコピーで Deathknell や退場時の能力を判定する（CR 371, 429.1.a.1.b, 479.1, 482）。
- Rebuttal は Energy が4以下の Spell を選ぶ。解決時に Power を支払ったプレイヤーが Spell のコントロールを得て、対象・モードなどを選び直すか決める。選び直しでは追加の費用を払わず、新たに選んだ対象の誘発を処理する。プレイを確定したプレイヤーと、解決時にコントロールしていたプレイヤーは別々に記録する（CR 420.4.a, 750–755）。
- Spell のプレイを監視する誘発は、Spell が解決したときに、その時点のコントローラーに対して判定する。Ravenbloom Student は、Rebuttal で奪った Spell と Rebuttal 自体の解決でそれぞれ誘発する。打ち消された Spell の確定履歴は Legion などで引き続き参照する（CR 420.4.a–b）。
- Hidden の Spell はプレイ確定時にカード本体が Chain に載る。伏せていた Battlefield は、対象の確定・再選択、Spell の効果による Unit の配置に適用する。別の場所を明示する対象にはその指定を適用する（CR 753.3, 811.1.d）。
- Rebuttal の解決中に基本 Rune と Reaction の Add 能力を使える。支払えるリソースが複数あれば選択でき、Add で発生した誘発は支払いと Spell の解決が終わるまで待つ（CR 334, 430.2, 445.2.c）。
- Main Phase 以外でも、Chain の優先権を持つプレイヤーは Reaction の起動型能力を使える。Hidden からのプレイと、それに対する Rebuttal もこのタイミングで行う（CR 337.4, 811.6, 813.1.c）。
- 167 枚すべてが `drafted`。

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

### Origins の Battlefields（2026-11-27）

- The Candlelit Sanctum は Conquer した席だけが山札の上2枚を見て、それぞれを残すか Recycle するか選ぶ。残すカードは選んだ順番で山札の上に置き、2枚とも Recycle するときは下に置く順番を抽選する。Predict と同じエンジンの処理を使う。
- Fortified Position は防御した席が選んだ Unit に Shield 2 を与える。戦闘終了時に Shield が消えることを、同じターンの状態で確認した。
- Altar to Unity、Aspirant’s Climb、Grove of the God-Willow、Navori Fighting Pit、Obelisk of Power、Startipped Peak、The Arena’s Greatest、Trifarian War Camp、Windswept Hillock も検証した。Origins の `full` は 298 枚中 69 枚、全体では 1,103 枚中 520 枚。[対戦シナリオ](../RiftboundTest/OriginsA.lean)

### Chosen Champion の実物カードの追跡（2026-11-27）

- 構築戦、Limited、Bo1 の登録で Chosen Champion の物理 ID を記録する。ゾーンを移動して ObjId が変わっても、登録したカードかどうかの判定が変わらないことを Lean で証明した。
- Back-Alley Bar は、いずれの席の Unit でも、効果によって戦場から Base に移動したときに Might が上がることを確認した。2枚を `full` とし、全体で1,103枚中522枚になった。[カード実装状況](coverage.md)

### Battlefield の誘発能力の対象、支払い、解決順（2026-11-27）

- Targon's Peak は Conquer した席を記録する。その席は、そのターンの Ending Phase に予約された能力を Chain に置く際に、任意の席の Rune を0〜2枚対象に取る。解決時にその Rune を Ready にする（CR 355.5.b）。Sigil of the Storm は解決時に自分の Rune 1枚を非対象の選択として Recycle する（CR 355.10.f）。Void Gate の追加ダメージは、その戦場の Unit に与えるダメージに適用する。[Origins の公式エラッタ](https://playriftbound.com/en-us/news/rules-and-releases/riftbound-origins-card-errata/)
- Monastery of Hirana は、Conquer した席が支配する Unit のバフを消費して能力を Chain に置き、解決時に1枚引く（CR 383.3.b、702.2.b.2）。
- Hallowed Tomb は、登録したカードと同名の Champion Unit を本人の Trash から選ぶ。戻す先の Champion Zone が空いている場合に置ける。登録した実物カードの ID はリプレイで引き続き照合する（CR 103.3.a.3、108.3.c.1）。[公式 Core Rules](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Vendetta の Jayce, Brilliant Inventor など6枚では、対象を1つ選んで能力を確定するか、能力を辞退する。Mask Mother の Energy は確定前に支払い、Might の上昇は解決時に適用する（CR 383.3.a–b）。
- Bandle Tree、Reaver's Row、Reckoner's Arena、Vilemaw's Lair、Zaun Warrens も対戦シナリオで確認した。Origins の `full` は298枚中80枚、全体では1,103枚中531枚。[カード実装状況](coverage.md)

### Origins の Battlefield の検証完了

- The Dreaming Tree は、Spell が味方 Unit を対象にした時点で、対象を選んだ席と Battlefield ごとにそのターンの初回を記録する。複数の Unit を一度に選んでも誘発は1回で、誘発が解決する前に対象を選び直しても初回の記録が残る。2対2ではチームメイトが支配する Unit も味方として扱う（CR 383.4.b、740.1.a）。[Origins 公式エラッタ](https://playriftbound.com/en-us/news/rules-and-releases/riftbound-origins-card-errata/)
- The Grand Plaza を Hold した席がそこに7体以上の Unit を支配していると、その誘発の解決時に勝つ。カードから得た勝利は得点を変えず、残りの処理を打ち切る。通常の Hold の得点はそれまでに処理する。2対2では同じチームの2席が勝者になる（CR 002、383.4.d）。
- Origins の Battlefield は24枚すべて `full`。Origins は298枚中82枚、全体では1,103枚中533枚が `full`。[カード実装状況](coverage.md)

### Unleashed の Bird をプレイする4枚

- Gutter Palace は手札の破棄と自身の消耗を起動時に支払う。Beginning Step では手札4枚と自身が支配する Battlefield 上の Unit 4体を確認し、勝利能力が解決すると Scoring Step に進む前にゲームが終わる（CR 315.2.a、423.3）。
- Flurry of Feathers のモードと対象は Spell の宣言時に選ぶ。Walking Roost は相手1席を対象にし、その席が Bird のプレイ先を選ぶ。Carrion Dredger の Deathknell では指定された Base に Bird を出す（CR 184.2、355.2、355.3、355.9）。
- Unleashed は225枚中57枚、全体では1,103枚中537枚が `full`。[カード実装状況](coverage.md)

### Conquer を生んだ戦闘の余剰ダメージ

- 攻撃側と防御側が敵 Unit に割り当てた致死量を超えるダメージを、それぞれ戦闘中の Battlefield に記録する。戦闘の Control Step で Conquer が起きたとき、誘発能力は割り当てた値を保持する。別の Battlefield の戦闘や無人の Battlefield の Conquer では、その値を参照しない（CR 467.2、468.5、383.4.c）。
- Piltover Enforcer は対象を選び、自身を消耗させて誘発能力を確定する。Sivir, Ambitious も対象を確定時に選び、解決時に記録された量のダメージを与える。[Unleashed 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/unleashed-rules-faq-and-clarifications/)
- Trapping Grounds、Yeti Brawler、Piltover Enforcer、Tryndamere, Barbarian、Sivir, Ambitious の5枚を `full` とし、全1,103枚中542枚を実装済みにした。[カード実装状況](coverage.md)

### 装備先で変わるコストと Ready の Sprite

- Hextech Gauntlets は、装備先の現在の Might を使って Equip の Energy を決める。Weaponmaster 経由では同じ Energy 割引に Weaponmaster の Power 割引を加える。装備先が Conquer すると、その戦闘の余剰ダメージが3点以上なら1枚引く（CR 356.4.g、818.1.c.4、821.1.c.2）。
- Bashful Bloom は、起動時に味方の Temporary Unit の数に応じて Energy を支払う。Bashful Bloom と Sprite Burst の Ready の Sprite は、プレイする席が Base または条件を満たす Battlefield に出す。Sprite Fountain と Sprite Queen は印刷された指定どおり Base に出す（CR 184.1、184.2、355.2）。
- Unleashed の5枚を `full` にし、全1,103枚中547枚を実装済みにした。[カード実装状況](coverage.md)

### 起動能力と Equip の XP コスト

- XP は、能力を起動する席が支払い、Chain に載った時点で差し引かれている。能力を打ち消しても、支払った XP は戻らない。Shepherd's Heirloom の Equip は XP 1 を支払う。Weaponmaster 経由でも同じ XP を支払う（CR 357.2、730.2、818.1.c.3、821.1.c.2）。
- Blood Rose の誘発では、Chain に載せるときに Energy 1 を支払うか選ぶ。Blood Rose と Voidreaver の起動では、対象を選んでから XP と Exhaust を支払う。Megatusk は自身と同じ場所にいる、自分が支配する Unit にそのターンの Ganking を与える。
- Unleashed の6枚を `full` にし、全1,103枚中553枚を実装済みにした。[カード実装状況](coverage.md)

### XP を支払う誘発能力と手札公開

- Kha'Zix, Evolving Hunter は攻撃時に対象を選び、誘発能力を確定する時点で XP 3 を支払う。解決時の Might でダメージを決める。Icevale Archer と Sinister Poro も攻撃時の対象を確定し、Energy 1 を支払ってから相手の応答に進む（CR 383.3.a、383.3.b、405.1）。
- Insightful Investigator は誘発を確定するときに相手を1人選ぶ。解決時にその相手の手札を公開し、公開を見てから XP 2 を支払うか決める。支払った場合は、選んだ相手が指定のカードを捨て、1枚引く（CR 204.3.a、383.3.b）。
- Unleashed の4枚を `full` にし、全1,103枚中557枚を実装済みにした。[カード実装状況](coverage.md)

### Elder Dragon のダメージと対象の場所

- ダメージが実際に通った時点で、それを与えた席を記録する。Elder Dragon は自身の支配者が敵 Unit に付けたダメージを致死とする。場に出る前のダメージも参照し、戦闘での致死量にはダメージを割り当てる席を使う（CR 142.3.b、142.4.c、418.6、467.2.c.5）。
- 登場時の能力では、Base と Battlefield ごとに最大1体を選ぶ。解決時に各対象の場所を照合し、元の場所を離れている対象を除いて同時にダメージを与える（CR 197、359.3.e）。[Unleashed 公式FAQ](https://playriftbound.com/en-us/news/rules-and-releases/unleashed-rules-faq-and-clarifications/)
- リプレイには、これまでの状態指紋に加えて、盤面に残るダメージを与えた席とその量を記録する。Elder Dragon を `full` とし、全1,103枚中558枚を実装済みにした。[カード実装状況](coverage.md)

### Showdown の開始を参照する Diana

- Diana, Lunari は、自身がいる Battlefield で Showdown が始まるたびに1回誘発する。戦闘に移らない Showdown も含む。Chain を解決して同じ Showdown に戻るときは、開始の処理を繰り返さない（CR 341-348）。
- Vendetta の訂正に従い、誘発を確定するときに Energy 1 を支払う。解決時に非公開の Predict を行い、その後の山札の一番上を公開する。公開したカードが Spell なら引く（CR 383.3.b）。[Vendetta 公式訂正](https://playriftbound.com/en-us/news/announcements/vendetta-errata-updates/)
- Diana, Lunari を `full` とし、全1,103枚中559枚を実装済みにした。[カード実装状況](coverage.md)

### 攻撃と防御で Fury を支払う Draven

- Draven, Vanquisher の攻撃・防御時の誘発は、Vendetta の訂正に従い、Chain を確定するときに Fury 1 を支払う。能力が解決した場合はそのターンの Might が2増える。攻撃側、防御側、支払いを辞退した場合、打ち消された場合を確認した（CR 383.3.b、405.1）。[Vendetta 公式訂正](https://playriftbound.com/en-us/news/announcements/vendetta-errata-updates/)
- Draven, Vanquisher を `full` とし、全1,103枚中560枚を実装済みにした。[カード実装状況](coverage.md)

### ユニットを手札に戻して誘発を確定する Emperor’s Dais

- Emperor’s Dais で Conquer した席は、能力を確定するときに Energy 1 を支払い、その Battlefield で自分が支配する Unit 1体をオーナーの手札に戻す。能力が解決すると、その Battlefield に Sand Soldier を Exhausted で出す。場所の異なる Unit、支払いの辞退、能力が打ち消された場合を確認した（CR 383.3、405.1）。[Vendetta 公式訂正](https://playriftbound.com/en-us/news/announcements/vendetta-errata-updates/)
- リプレイの操作履歴には、支払った Energy と、コストとして手札に戻した Unit が表示される。Emperor’s Dais を `full` とし、全1,103枚中561枚を実装済みにした。[カード実装状況](coverage.md)

### 追加コストを支払って Battlefield に出す

- Battlefield を指定する手では、配置先と追加コストに使うカードを別々に選ぶ。Cruel Patron は必須の Kill を支払い、Skystrike Squadron は Gear の返却を選んだときに減額される。配置先や追加コストのオブジェクトは、呪文による対象選択として記録しない（CR 355、356、357）。
- Stalking Wolf は、自分の最後の Unit が支払いに使うペットである Battlefield に Ambush できる。Chain への Reaction、Base へのプレイ、効果によるプレイを確認した。Stalking Wolf を `full` とし、全1,103枚中562枚を実装済みにした（CR 822）。[Vendetta 公式訂正](https://playriftbound.com/en-us/news/announcements/vendetta-errata-updates/) · [カード実装状況](coverage.md)
- 旧形式のリプレイは `revalidate` で更新できる。盤面の指紋とイベント列を照合し、実際にプレイした Unit や Gear の配置先・追加コストを呪文の対象として記録していた場合だけ、その注記を取り除く。

### Fizz で唱え直した呪文を山札の底に戻す

- Fizz, Trickster の誘発は確定前に辞退できる。解決時には自身の Trash から Energy の元のコストが3以下の Spell を選び、Energy を免除して Power を支払う（CR 383.3.a、420.3）。[Vendetta 公式訂正](https://playriftbound.com/en-us/news/announcements/vendetta-errata-updates/)
- 確定した Spell が解決や打ち消しで Chain を離れるときは、オーナーの山札の底へ直接 Recycle する。Spell 自身の指示で Chain を離れる場合はその指示を適用する。Fizz, Trickster を `full` とし、全1,103枚中563枚を実装済みにした（CR 391.3.a、417）。[Vendetta 公式ルール更新](https://playriftbound.com/en-us/news/announcements/core-rules-vendetta-patch-notes/) · [カード実装状況](coverage.md)

### Janna がいる場所での回復と移動

- Janna, Savior の誘発を確定するとき、同じ場所から Base に移す敵 Unit を最大1体選ぶ。対象を選ばずに回復でき、選んだ対象が解決時に無効なら、その対象の移動だけを行わない。[Spiritforged 公式FAQ](https://playriftbound.com/en-us/news/rules-and-releases/riftbound-spiritforged-faq/)
- 解決時に Janna と同じ場所で支配している Unit のダメージをすべて除き、取り除いた量を記録する。Janna, Savior を `full` とし、全1,103枚中564枚を実装済みにした（CR 419）。[カード実装状況](coverage.md)

### Guardian Angel の身代わりと回復順

- Guardian Angel を装備した Unit が死ぬ場合、その Gear が代わりに死ぬ。Unit は回復、消耗、Recall の順に処理される。実際に取り除いたダメージ量を記録し、Recall では Standard Move のイベントを発生させない（CR 373、419、456、825）。[Riftbound 公式総合ルール](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Combat では両軍の割り当て済みダメージを記録してから、Combat Cleanup で致死と身代わりを処理する（CR 323.4、467.2.d、468.1）。
- Soraka などで Base にいる Unit を救った場合は、回復と消耗を記録する。Guardian Angel を `full` とし、全1,103枚中565枚を実装済みにした。[カード実装状況](coverage.md)

### Origins のダメージ呪文の対象確認

- Hextech Ray、Void Seeker、Falling Comet は、解決時に対象が Battlefield にいるか確認する。Void Seeker は、Flash で対象が Base に戻った場合もドローを実行する（CR 359.3.e.5）。[Riftbound 公式総合ルール](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Singularity は確定時に異なる Unit を最大2体選ぶ。解決時に残った対象それぞれへ同時に6ダメージを与える。以上4枚を `full` とし、全1,103枚中569枚を実装済みにした。[カード実装状況](coverage.md)

### Falling Star の2回のダメージと Rocket Barrage の Repeat

- Falling Star は2回のダメージそれぞれの対象を確定し、解決時に対象を再確認する。同じ Unit を選び、その Unit が有効な対象であれば、3ダメージを2回与える（CR 359.3.e、758.2）。[Riftbound 公式総合ルール](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Rocket Barrage の Repeat はモードと対象を実行ごとに確定する。同じ Gear が2回選ばれた場合は1回目に死に、2回目は解決時の対象確認で処理を省く（CR 820.2.a）。以上2枚を `full` とし、全1,103枚中571枚を実装済みにした。[カード実装状況](coverage.md)

### Bellows Breath の同じ場所と Piercing Light の2つの対象

- Bellows Breath は1つの Base または Battlefield から異なる Unit を最大3体選べる。対象が複数の場所に分かれた場合は、解決時に元の対象がいる場所を1つ選ぶ（CR 355.11、355.13、359.3.e.8）。[Riftbound 公式総合ルール](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Piercing Light の1体目が Battlefield を離れた場合、2体目へのダメージは対象が有効であれば実行する。以上2枚を `full` とし、全1,103枚中573枚を実装済みにした。[カード実装状況](coverage.md)

### Beginning Phase の誘発と Temporary

- Temporary は Beginning Phase に Chain へ載り、得点前に解決する。同じ開始時点に自分がコントロールする誘発は順序を選べ、対戦相手は解決前に Reaction を使える。FFA で複数の席がコントロールする誘発はターン順で載せる（CR 315.2.a、383、816）。[Riftbound 公式総合ルール](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Dusk Rose Lab は支配者のターンに誘発し、同じ Battlefield にいる自分の Unit を能力の確定時に Kill する。Frozen Fortress は各ターンに誘発し、支配者がいればその席が能力をコントロールする。Petricite Monument の Deflect は Temporary の解決で Gear が死ぬまで続く（CR 190.6、383.3、740）。以上3枚を `full` とし、全1,103枚中576枚を実装済みにした。[カード実装状況](coverage.md)
- 新しい誘発から Chain を開始するときと、解決後に次の Chain 項目が残るときは、その項目のコントローラーに優先権を渡す（CR 337.4、340.4）。

### Temporary のコピー、入れ替え、得点時の誘発

- Keeper of Masks の Reflection は Keeper のコピーになり、元のオブジェクトと同じ Beginning Phase に Temporary が誘発する。LeBlanc は自身の支配者が同じ Battlefield でコントロールする Temporary だけを抑止する。
- Smoke and Mirrors は自分がコントロールする別々の場所の Unit を選ぶ。Temporary を持つ対象がいない場合も1枚引く。Sumpworks Map は Reaction でプレイでき、残っている間は相手の Hold と Conquer で引く。以上4枚を `full` とし、全1,103枚中580枚を実装済みにした。[カード実装状況](coverage.md)

### 移動を誘発した出発地点

- Lillia, Fae Fawn は誘発した移動の出発地点を保持する。最初の能力に Flash を重ねて移動した場合、各能力が自分の出発地点に Sprite を作る。カードを `full` とし、全1,103枚中581枚を実装済みにした。[カード実装状況](coverage.md)

### 単独防衛と誘発元の Spell の支払い

- Forbidding Waste では単独で防衛している Unit の Might が2下がる。同じ Battlefield にチームメイトの Unit がいる場合は下がらない。
- Revna the Lorekeeper と Forgotten Library の誘発は、解決した Spell の確定時に本人が支払った Energy を調べる。同じターンに別の Spell に支払った Energy は参照しない。以上3枚を `full` とし、全1,103枚中584枚が実装済みとなった。[カード実装状況](coverage.md)

### 味方の Gear を戻すコストと移動誘発

- Legion Quartermaster、Spirit of the Forge、Skystrike Squadron は、2対2でチームメイトがコントロールする Gear も追加コストに使える。Gear はオーナーの手札に戻る。コストに選んだ Gear は対象として扱わない（CR 355.10.c、740.1.a）。[Riftbound 公式総合ルール](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Ribbon Dancer、Corrupt Enforcer、Harpoon Squad、Mister Root はカードごとの移動方向で誘発する。Reflection はコピー元を指定する効果と組み合わせ、コピー元のプレイ時の能力を再度誘発させない。今回の6枚を `full` とし、全1,103枚中590枚が実装済みとなった。[カード実装状況](coverage.md)

### 戦場に移動したときの誘発

- Noxian Drummer と Corina Veraza は、移動イベントの行き先が戦場である場合に誘発する。Base に戻る移動では誘発しない。
- 効果の「ここ」は解決時に参照する。Corina が最初の誘発に対する Flash で Base に戻った場合、Recruit 3体は Base に出る。2枚を `full` とし、全1,103枚中592枚が実装済みになった。[公式総合ルール 359.3.f](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf#page=60)

### 移動先を限定しない誘発

- Apprentice Smith は公開した山札の一番上が Gear なら正式な Draw として手札に加え、それ以外は Recycle する。Traveling Merchant はディスカードを先に選んでから引く。
- Stellacorn Herder は移動ごとに1枚引き、Treasure Hunter は移動ごとに Exhaust した Gold を出す。Gold の消費と Power の追加も検証した。Nilah, Joyful Ascetic は戦場間の Ganking を含め、移動ごとに1 XPを得る。6枚を `full` とし、全1,103枚中598枚が実装済みになった。

### 2対2で味方の Unit を使う追加コスト

- Ki Burst と Life from Stone はチームメイトの Ready Unit を Exhaust して支払える。Parallel Convergence と Ekko, Ingenious はチームメイトがコントロールする Unit も選べ、支払い時にオーナーの手札へ戻す。Starry-Eyed Songstress の割引でもチームメイトの Ready Unit を使える。呪文の対象は追加コストとは別に記録する。[公式総合ルール 355.10.c、415.4、740.1.a](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### Unit や Gear を手札に戻す追加コストの順序

- Unit や Gear を戻す追加コストは、プレイするカードが盤面に出る前に支払う。カードを効果によってプレイする場合も同じ順序になる。宣言時に確定した支払いを維持し、Ready で出るかは支払い後の盤面で判定する。Firebrand Raider を戻して Ekko, Ingenious をプレイした場合、Ekko は Exhaust して出る（CR 357、359.2）。[Riftbound 公式総合ルール](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### 移動誘発が参照する行き先

- Fae Porter と Irresistible Faefolk は移動先の戦場を誘発に記録する。Flash で元の Unit が Base に戻っても、選んだ Unit は最初の戦場へ移動する。Fae Porter は確定時に Chaos Power を支払い、自分がコントロールする Unit を選ぶ。2枚を `full` とし、全1,103枚中600枚が実装済みとなった。[公式総合ルール 359.3.f.3、383.3](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### Kill・Exhaust・XP の追加コストと登場順

- Unit や Gear をプレイする際の Kill・Exhaust・XP の追加コストを盤面に出る前に支払う。効果によるプレイも同じ順序を使う。Firebrand Raider を Kill して Cruel Patron を出すと Exhaust し、Hourglass が Raider を救った場合は Raider の効果が残るので Ready で出る。置換があっても Kill のコストは支払い済みになる（CR 357.2.a、359.2）。[Riftbound 公式総合ルール](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### 味方を選んだときの誘発と防衛への合流

- Spirit Wheel と Blade Dancer は2対2でチームメイトの Unit を選んだときにも誘発する。任意の支払いと Exhaust は確定時に行い、Draw と Ready は解決時に処理する。Loyal Pup の合流も確定時に選ぶ。Ruin Runner と Cleave を含む5枚を `full` とし、全1,103枚中605枚が実装済みとなった。

### Might と移動に関わる Origins のカード

- Wizened Elder、Orb of Regret、Smoke Screen、Stupefy、Arena Bar、Bilgewater Bully、Cithria of Cloudfield、Taric, Protector、Captain Farron の9枚を `full` とした。Buff した Bilgewater Bully が Ready になると戦場から別の戦場へ移動できる。Taric と Captain Farron の効果は2対2で同じ戦場にいるチームメイトにも適用される。全1,103枚中614枚が実装済みとなった。

### Unit・Gear の登場前に行うディスカード

- Unit や Gear を直接または効果でプレイするときに任意のディスカードを選んだ場合、手札を捨ててから盤面に出す。Zed, From the Shadows を手札と Void Rush の両方からプレイし、ディスカード、登場、Shadow Clone の誘発を確認する。Void Rush を `full` とし、全1,103枚中615枚が実装済みとなった。

### Poro Herder の誘発条件と Iron Ballista の登場

- Poro Herder は自分がコントロールする Poro を登場時に確認する。Retreat でその Poro を手札に戻しても、Chain に載った能力は解決する。Iron Ballista は登場時点で Exhaust している。Pit Crew、Ravenbloom Student、Fight or Flight、Bounty Hunter を含む6枚を `full` とし、全1,103枚中621枚が実装済みとなった。[公式総合ルール 383.2.a.1、359.3](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### 得点と戦場の Unit を参照する誘発

- Poppy, Paragon は登場時に各対戦相手の得点を確認する。War でも手番順の後ろにいる対戦相手が勝利点まで3点以内なら能力が誘発する。Kha'Zix, Mutating Horror は攻撃・防衛の開始時に、戦場の敵 Unit が1体かどうかを確認する。2枚を `full` とし、全1,103枚中623枚が実装済みとなった。[公式総合ルール 383.2.a.1](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### Unit・Gear の登場後に行う Cleanup

- 通常の優先権で Unit や Gear をプレイした後、優先権を返す前に Cleanup を行う。Cruel Patron のコストで Lee Sin を Kill すると、Might が下がって致死ダメージに達した味方の Unit もこの時点で撃破される。Lee Sin, Centered の Accelerate と Buff 済みの味方への効果を確認して `full` とし、全1,103枚中624枚が実装済みとなった。[公式総合ルール 322–323](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

- Reaction などで Unit や Gear を出して Chain に応じた場合も、次の応答より前に Cleanup を行う。進行性の証明はこの Cleanup を経て決定点に戻る経路を含む。

### 同じ効果で複数の Unit に与えるダメージ

- Cannon Barrage と Anivia, Primal は対象の敵 Unit すべてにダメージを与え、Cleanup で撃破を処理する。2枚を `full` とし、全1,103枚中626枚が実装済みとなった。

### Origins の Legion と登場時の Ready

- Magma Wurm は2対2でチームメイトの Unit が登場するときにも適用される。カードとトークンの両方で確認した。「あなたの」と書かれた Renata Glasc、Wuju Master の対象は各カードの支配者に限る。Chemtech Enforcer、Sky Splitter、Dangerous Duo、Raging Soul、Scrapyard Champion、Confront と合わせて7枚を `full` とし、全1,103枚中633枚が実装済みとなった。
- `applyFrame0_permanentPlay_cleanup` により、フレームの処理が Unit・Gear の直接プレイを受理したときに、次の処理が Cleanup になることを証明した。通常の優先権、Chain、Showdown を含む。

### Spiritforged の味方と支配者

- Bushwhack はそのターンに味方がプレイする Unit と Unit トークンの登場に適用する。Production Surge は使った席が支配する Mech で値引きする。Against the Odds、Eager Drakehound、Blast Corps Cadet、Ferrous Forerunner、Vex, Cheerless と合わせて7枚を `full` とし、全1,103枚中640枚が実装済みとなった。
- I10 のマリガンと通常のディスカードについて、同じ手札の表示と選択枚数から同じ数の合法手が得られることを証明した。

### Spiritforged の装備・配置・戦闘

- Serrated Dirk、Minotaur Reckoner、Perched Grimwyrm、Sudden Storm、Rengar, Pouncing、Lucian, Gunslinger、Skyfall of Areion を確認した。Rengar はすでに項目がある Chain に Reaction として応答し、自分が攻撃している Battlefield に出られる。全1,103枚中647枚を `full` とした。
- 自動対戦の Driver は、強制手だけで同じ状態に戻ることを検査した場合に、ジャッジの引き分けを送る。識別子を付け替えた状態を検出する処理は残っている。

### Brazen Buccaneer のディスカード

- Brazen Buccaneer は手札を1枚捨てる追加コストを選んだときに2 Energy少なく支払い、その後に登場する。通常のプレイと、効果によってプレイするときの見積もりを確認した。全1,103枚中648枚が実装済みとなった。

### Trash から登場する任意誘発

- Flame Chompers と Immortal Phoenix の支払いは、解決時ではなく誘発を確定するときに行う。Brazen Buccaneer のコストで Flame Chompers を捨てる場合は、Brazen が登場してから Flame Chompers の支払いを選ぶ。2枚を `full` とし、全1,103枚中650枚が実装済みになった。[公式総合ルール 383.3](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### Unleashed のドローと登場条件

- Right of Conquest は自分かチームメイトが支配する Battlefield で枚数を数える。Towering Pairofant は、チームメイトが支配していた Unit が死んだターンにも Ready で登場する。Arena Kingpin、Vault Breaker、Monster Harpoon、Scorchclaw、Jhin, Murderous Artist を合わせて7枚を `full` とし、全1,103枚中657枚を実装済みとした。

### 呪文ごとのエナジー支払い

- 呪文の費用を確定した席と支払ったエナジーをプレイ履歴に記録する。Prepared Neophyte は、その席が同じターンに1つの呪文に4エナジー以上払ったときに強化される。所有者が別の席でも、また同じカードを値引きして再度プレイしても、最初の支払いが残る。全1,103枚中658枚が実装済みになった。

### プレイ履歴と物理カードの識別

- Legion はその席がプレイを確定した別の物理カードを数える。手札に戻った同じカードと、同じ名前の別の1枚を区別する。再照合では、プレイの確定時に保存した物理カードIDも確認できる。[公式総合ルール 812.1.c](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### Unleashed の Repeat と手札の入れ替え

- Upstage Comedy は Repeat の支払いと2回分の対象をプレイ時に選ぶ。Concentrate はプレイした席の XP で費用が決まり、Evershade Stalker と Lunar Boon はカードを捨ててから引く。4枚を `full` とし、全1,103枚中662枚を実装済みとした。

### Origins の得点と戦闘、Hidden、対象の確認

- Draven, Showboat は2v2でチームの得点を参照する。Raging Firebrand の値引きは次の Spell まで残り、Kai'Sa, Survivor は Accelerate を払った場合に Ready で登場し、自身の Battlefield の Conquer で引く。Wielder of Water は単独で攻撃・防御するときに強化される。Sprite Call は Hidden からも Ready の Sprite を Base に出し、Vengeance は両陣営の Unit を対象にできる。6枚を `full` とし、全1,103枚中668枚を実装済みとした。

### Origins のプレイ時効果と誘発条件

- Kadregrin the Infernal はプレイした席が支配する Mighty Unit を数える。Sett, Kingpin は自身が Battlefield にいる場合だけ、同じ Battlefield にいる味方の Buff 付き Unit を数える。Discipline は対象を失っても独立したドローを実行する。Wind Wall、Ahri, Alluring、Thousand-Tailed Watcher、Mobilize、Qiyana, Victorious、Scrapheap、Teemo, Scout を合わせて10枚を `full` とし、全1,103枚中678枚を実装済みとした（CR 359.3.e、491.8.c、491.8.e）。

### 次の Spell を確定した席と時点

- 次の Spell の値引きは、カードのオーナーと別の席が効果でプレイする場合も、実際にプレイを確定した席のものを消費する。プレイの確定時点を履歴に保存し、リプレイでも照合できる。

### Spiritforged の装備、Repeat と誘発

- Blood Rush の2回分は別々の対象を選べ、Assault はターン終了時に切れる。Cloth Armor は Quick-Draw で登場時に装着でき、通常の Equip は外れている間に Mind の Power を使う。Experimental Hexplate の Mech は装備している間だけ有効。Factory Recall は装備中の敵 Gear もオーナーの手札に戻す。Lucian, Merciless、Black Market Broker、Sandshifter を合わせて7枚を `full` とし、全1,103枚中685枚を実装済みとした。[Spiritforged 公式エラッタ](https://playriftbound.com/en-us/news/rules-and-releases/riftbound-spiritforged-errata/)
- Counter Strike は敵 Unit のダメージを一度防いでから自分が引くケースを確認した。公式ギャラリーの取得データは1 Power のドメインを特定できないため、費用を確認するまで `drafted` とする。

### Spiritforged の起動コスト、Reaction と Deathknell

- Poro Snax は能力の宣言で自身をキルしてから Chain に能力を置き、解決時にカードを引く。Premonition は相手の Spell に応答でき、先に解決して自身の席だけが3枚引く。Feral Strength、Frigid Touch、Punch First、Lonely Poro、Honest Broker を合わせて7枚を `full` とし、全1,103枚中692枚を実装済みとした。

### Buff を行った席

- Simian Ancestor は自身を支配する席が Buff したときに誘発する。Mistfall は自身を支配する席が味方の Unit を Buff したとき、Body の Power を払い Gear を Exhaust する選択を誘発の確定時に出す。リプレイでは Buff を行った席も照合できる。2枚を `full` とし、全1,103枚中694枚を実装済みとした。[公式総合ルール 412.4、702.2.a](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### Spiritforged の装備と Conquer

- Doran's Shield を装備した Unit は最初に戦闘ダメージを割り当てられる。Boots of Swiftness は Battlefield 間の通常移動を許し、移動後に Unit は Exhaust する。Plundering Poro と Cull は装備先や自身の Conquer で Exhaust 済みの Gold を出し、Doran's Ring は捨て札の回答後に引く。5枚を `full` とし、全1,103枚中699枚を実装済みとした。
- Hexdrinker は付いている間だけ Deflect を与え、敵の Spell の支払いに Power を一つ加える。複数ドメインの Power がある場合、エンジンが消費するドメインを固定順で選ぶ。支払い元を選べるようにするまで `drafted` とする。

### ターン中の伏せ札の閲覧

- Scuttle Crab はプレイ時に引く。Deathknell では選んだ敵の手札を公開し、その敵が支配する伏せ札をターン中に閲覧できる権限を自身の支配者に与え、1 XP を加える。Lean では新たに閲覧できる札が Hidden ゾーンにあり、権限の席・ターン・支配者が一致することを証明した。2v2 の選択肢と、対局リプレイで閲覧権が切れることを確認し、全1,103枚中700枚を `full` とした。[公式総合ルール 128.2.a、129.4](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### Unleashed の戦闘、XP と Repeat

- Yuumi, Magical Cat が攻撃または防御するときは、同じ Battlefield にいる自身の支配者の別の Unit に +3 Might と Tank をターン終了まで与える。Lillia, Protector of Dreams の Tank とトークンのプレイも自身の支配者のものに限る。Master Yi, Unstoppable は到達した最も高い段階の費用軽減を使い、XP 16 で敵から選ばれなくなる。Downstage Dramatics は Reaction で割り込み、Repeat を払うと2枚引く。4枚を確認し、全1,103枚中704枚を `full` とした。

### Stun を行った席

- Eclipse Herald と Vex, Mocking は、自身の支配者が敵の Unit を Stun したときに誘発する。Vex の選択は誘発を確定する時点で行い、Stun された Unit が移動しても、その時点の Battlefield を移動先として使う。リプレイでは Stun を行った席を記録する。2枚を確認し、全1,103枚中706枚を `full` とした。[公式総合ルール 383.3.a、412.4、424](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### 同時に動かす対象と同時に Stun された対象

- Tricksy Tentacles は、同じ敵が支配する合計 Might 8 以下の Unit と一つの移動先を宣言する。解決時に元の対象を再確認し、条件を満たすまで対象を減らす必要がある場合はプレイヤーが残す対象を選ぶ。宣言した Base が支配者の変更で無効になった場合や、War で移動先の Battlefield が塞がった場合は Recall を適用する。[公式総合ルール 355.4、355.11、449.2.c](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Radiant Dawn は自身の支配者が一度に複数の敵を Stun しても一度誘発し、味方を Buff する。Solari Chief は敵を指名し、解決時に Stun 済みならキルし、そうでなければ Stun する。3枚を確認し、全1,103枚中709枚を `full` とした。[公式総合ルール 355.4、383.3.a、424](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### チーム戦の対象と同時ダメージ

- En Garde は味方を選べ、追加の +1 Might には術者自身がその場で支配する唯一の Unit を選ぶ必要がある。Kinkou Monk は二体までの対象を誘発の確定時にまとめて選ぶ。Clash of Giants は二体の Unit が互いに同時にダメージを与える。The Ruination は全席の Unit を同時にキルし、死亡置換を適用する。Block、Blastcone Fae、Ember Monk、Kog'Maw, Caustic と合わせて8枚を確認し、全1,103枚中717枚を `full` とした。[公式総合ルール 355、370、418.6.b.3](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- 可変 Power の支払いでは、残高と指定された記号を満たすドメインの組み合わせが、ドメイン順で列挙されることを証明した。通常のグループ移動では、候補、費用の可否、宣言済みグループを確定できるかが対応していれば、オブジェクトの ID を付け替えても提示される回答が対応する。[可変 Power の証明](../Riftbound/Invariant/FlexiblePaymentChoices.lean) [移動の選択の証明](../Riftbound/Invariant/PrivateChoices.lean)

### Chain の対象と同時に死亡した Unit

- Not So Fast は味方の Unit や Gear を選んだ敵の Chain 項目を打ち消す。Drag Under は解決時に対象が Battlefield にいることを再確認する。Moonlight Affliction で Might が0以下になった Unit も、ダメージが付いていれば Cleanup でキルされる。Dune Drake、Warwick, Hunter、Trifarian Gloryseeker、Loyal Poro を合わせて7枚を確認し、全1,103枚中724枚を `full` とした。[公式総合ルール 142.4.b、359.3.e、418.6.b.3](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- 同時に死亡した各 Unit について、死亡の処理を始める直前に同じ場所に味方がいたかを記録する。この記録を、Loyal Poro と Lonely Poro の Deathknell が使う。Battlefield の味方にはチームメイトの Unit も含まれる。
- 映像の観測には手番号の範囲を指定できる。Basic Rune の操作はコードと Exhaust の有無で照合できる。Power の処理では、指定された一つの残高から引いた量と、他の残高が変わらないことを証明した。[リプレイの入力形式](viewer.md) [Power の証明](../Riftbound/State/Pool.lean)

### 手札を公開する席とトークンの支配者

- Mindsplitter は誘発の対象にした相手の手札を公開し、その手札から選んだ1枚を捨てさせる。Machine Evangel は自分の Base に Recruit を3体出す。Renata Glasc, Industrialist は自分のトークンを Ready で登場させる。Danger Zone は Repeat を選べて、自分が支配する Mech だけを強化する。
- Bandle Soldier の追加効果は自分の XP で決まり、Scrutinizing Sergeant は自分自身とチームメイトを含む味方の Unit を数える。6枚を確認し、全1,103枚中730枚を `full` とした。

### 敵がいる Battlefield へのプレイ

- 敵の Unit がいる場所への Ambush を Rengar, Trophy Hunter に適用する。通常の配置先と Reaction の両方でこの許可を確認する。Dauntless Vanguard の配置先にも敵の Unit が必要になる。[Unleashed 公式訂正](https://playriftbound.com/en-us/news/rules-and-releases/unleashed-errata-updates/) [公式総合ルール 822.1.d](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Arachnoid Horror は同じ場所に他の味方 Unit がいない敵を探す。チームメイトもこの配置の許可を使える。敵の Unit に付いた Gear があっても、Unit が一人かどうかの判定は変わらない。[公式総合ルール 740.2.a](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### 追加費用、戦闘と開始フェイズ

- Clockwork Keeper は追加の Calm Power を選んで払ったときに引く。Yasuo, Remorseful の誘発は、解決時の自身の Might と所在地、誘発自体の支配者を使う。Lee Sin, Ascetic の Shield は防御中だけ働き、複数の Buff を置ける。[公式総合ルール 359.3.f、814](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Mushroom Pouch は自分が伏せ札を持つ自分の Beginning Phase に引く。Buhru Captain は引く、Buff する、見送るの3通りを選べる。Yordle Explorer は自身の支配者が印刷の Power 費用2以上のカードをプレイすると引く。

### 装備が与えた死亡時の能力

- Sacred Shears の Deathknell は装備された Unit の能力として働く。死亡直前の装備を参照し、同時に Gear が取り除かれた場合も処理する。Gear だけが死亡した場合と、死亡を追放で置き換えた場合は引かない。[公式総合ルール 429.1.a.1.b、808](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### Hidden の制約とカードを使った席

- Noxus Saboteur は同じ Battlefield にある敵の伏せ札の公開を防ぐ。Brynhir Thundersong の効果は敵が伏せ札から Unit や Spell をプレイする場合にも適用する。Basic Rune の起動は許される。
- Katarina, Reckless は自身の支配者が Hide したときに Ready になり、伏せ札からのプレイが解決したときに敵の Unit にダメージを与える。Rumble, Scrapper は自身の支配者の Mech だけを強化し、自分の Hold で Mech を出す。Sacred Shears と合わせて5枚を確認し、全1,103枚中744枚を `full` とした。

### 手札の確認時点と Gear の起動

- Loose Cannon は自分の Beginning Phase に誘発し、解決するときに手札の枚数を確認する。Jinx, Rebel は同じ処理で複数枚を捨てても1回だけ Ready になり、Might が1増える。[Unleashed 公式FAQ](https://playriftbound.com/en-us/news/rules-and-releases/unleashed-rules-faq-and-clarifications/)
- Leona, Determined は攻撃した場所にいる敵の Unit を対象にする。Royal Entourage は自分や相手の Legend を Ready または Exhaust にできる。Prize of Progress はコストで Gear 自体を破壊する起動も検出する。5枚を確認し、全1,103枚中749枚を `full` とした。

### 同じターンの Power 支払いの集計

- Lean で、Main Phase への移行が任意の席の支払い履歴を過不足なく引き継ぎ、ターン終了が所持資源と支払い履歴を消去することを証明した。[TurnPhaseWork.lean](../Riftbound/Invariant/TurnPhaseWork.lean)
- Deflect と Accelerate で払った Power は、そのターンの支払いに含める。Main Phase の開始で Rune Pool を空にするときは、それまでに支払った量を席ごとに引き継ぐ。Sivir, Mercenary は同じターンに自身の支配者が払った量を参照する。リプレイでは支払いの合計を照合できる。[公式総合ルール 167、316.3、809](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Viktor, Leader は味方の Unit が同時に死亡すれば1体ずつ数え、自身も同じ処理で死亡した場合は誘発しない。Rhasa the Sunderer は自身のプレイヤーの Trash で値引きを算出する。Darius, Trifarian と Ancient Warmonger はそれぞれ同じ Battlefield の味方と敵を確認する。Yasuo, Windrider、Fiora, Victorious、Gearhead、Fae Dragon を含む9枚を確認し、全1,103枚中758枚を `full` とした。[公式総合ルール 383.2.c.2](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

### Deathknell の Recycle と支配者ごとの効果

- Ekko, Recurrent は Deathknell の確定時に自身を Recycle し、解決時に能力の支配者の Rune を Ready にする。確定前に Ekko が Trash を離れた場合、Recycle の費用は払えない。[公式総合ルール 204.1.c、383.3.b、417](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)
- Herald of Scales の値引きと Trusty Ramhound の Might は、そのカードの支配者に対応する。Deflect と Weaponmaster の Ornn, Forge God、Hexdrinker、Unsung Hero、Hand of Noxus を含む7枚を確認し、全1,103枚中765枚を `full` とした。

### Buff と XP のカウンター

- 通常の Unit に2つ目の Buff を加えようとしても、その Unit の状態は変わらず追加の Buff イベントも発生しない。XP の獲得と支払いは対象の席の残高だけを変える。これらを Lean で証明し、印刷された Buff と XP Tracker を `full` とした。[証明](../Riftbound/Invariant/GameCounters.lean) [公式総合ルール 702.3、729、730](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf)

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

### カードのプレイと起動型能力の速度

- 能力を指す矢印付きの Action と Reaction は、カード本体のキーワードに含めない。Unleashed 以降の該当15枚を再生成した。[Unleashed の公式パッチノート](https://playriftbound.com/en-us/news/rules-and-releases/riftbound-core-rules-unleashed-patch-notes/)
- Dragonsoul Sage と Energy Conduit は通常の優先権でプレイできる。盤面からの Add は Chain、Showdown、2対2の招待でも即時に解決し、起動した席だけに Energy を追加する。
- Divining Shells は起動時に消耗と Kill を支払う。対象の Might は解決時に上がり、ターン終了時に戻る。Vision の閲覧と Recycle の選択を含め、以上3枚を `full` とした。[PrintedAbilitySpeed.lean](../RiftboundTest/PrintedAbilitySpeed.lean)

### Honeyfruit の Level 6 と複数の資源を加える Add

- 固定量の Energy や Power を複数加える起動型能力を、ひとつの即時 Add として解決する。途中にドローなどの別の指示がある効果は通常の解決を使う。効果中の支払い候補にも、Add で増える資源の合計を反映する（CR 430.2）。[公式パッチノート](https://playriftbound.com/en-us/news/rules-and-releases/riftbound-core-rules-patch-notes/)
- Honeyfruit は 6 XP 以上のとき、消耗して Power を1つ加える通常の能力か、消耗して Energy と Power を1つずつ加える Level 6 の能力を選べる。Chain と Showdown での即時 Add、両方の資源を要求する支払い、5 XP での起動拒否を確認し、`full` にした。[UnleashedA.lean](../RiftboundTest/UnleashedA.lean)

### 誘発能力の確定と2v2での味方判定（2026-11-27）

- 誘発の冒頭で選べる消耗コストは、能力を確定して Chain に載せるときに払う（CR 383.3.a, 383.3.b.1, 740.4.a.2）。Altar of Memories、Chemtech Cask、Battle Mistress、Grand Duelist、Relentless Storm、Fresh Beans をこの方式で実装し、各シナリオを検証して `full` にした。
- 誘発は、イベントに記録された席をもとに陣営を判定する。「味方」は2v2のチームメイトも含み、「敵」は相手チームに限る。「あなた」が行う操作を条件とするカードは本人に限る（CR 491.8.e, 740.1）。Chemtech Cask は本人が対戦相手のターンに呪文をプレイしたときに誘発する。
- Altar of Memories は消耗を済ませてから、解決時に引いたカードも含めて自分の手札から戻すカードを選ぶ。Battle Mistress は同時に複数の敵 Unit が死んだ場合に1回だけ誘発する。Relentless Storm と Fresh Beans は条件を満たす Unit トークンのプレイも見る。

### Hold・Conquer の誘発（2026-11-27）

- Chem-Baroness と Gloomist は、本人か味方の Hold で誘発する。消耗を払う席と効果を受ける席は、その能力のコントローラー。Blue Sentinel が増やすのは Hold を行った席の誘発で、味方の誘発は増えない（CR 383.3, 491.8）。
- Hall of Legends、Sunken Temple、Treasure Hoard は、能力を確定するときに Energy を払う（CR 383.3.b.1）。Sunken Temple は Conquer 時の Might を判定し、解決までにその Unit の Might が下がっても引く。
- The Papertree は2v2でも全席がそれぞれの山札から Rune を1枚ずつ消耗状態で出す。以上6枚を `full` にした。

### Vex, Apathetic の移動制限（2026-11-27）

- Vex が Battlefield にいる間、対戦相手が Unit カードか Unit トークンをプレイすると誘発する。両方を1つの誘発で扱い、Champion Zone からプレイする能力の番号を維持する。対象を Stun し、そのターンはその Unit をプレイした席からの Standard Move と効果による Move を止める（CR 424, 447–449）。
- コントロールが変わっても制限を受ける席は変わらない。別の席が動かす場合や Recall では、この制限を適用しない。ターンが進むか、カードが Board を離れて別のオブジェクトとして戻ると制限は切れる（CR 448.1, 456）。1v1 と2v2のシナリオを追加し、`full` にした。

### 一斉移動の費用と Mageseeker Investigator（2026-11-27）

- 同じ Battlefield に一斉に移動する2体目以降に、Mageseeker Investigator 1体ごとに Power 1 がかかる。Gravity Field の固定費用は移動先ごとに加算する。2v2の味方にはどちらの費用もかからない（CR 144.3, 204.4, 491.8）。
- Standard Move は選択したユニット数と支払いが一致した時点で一斉に移動する。効果で動かす場合は実際に到着するユニットを数え、効果を指示された席がその場で Add を使える。支払いを見送ると、選びかけた Add と移動は取り消される（CR 204.4.b.1, 204.4.c, 412）。
- Standard Move の記録では、必要な Add を行ってから移動先と支払いを宣言する。効果の解決中に移動費用を払う場合は、選んだ Add と支払いの確定を記録する。
- Azir, Sovereign は自分のトークンを能力の確定時に選び、解決時に Azir がいる Battlefield にまとめて動かす。Amateur Recital は Hold の能力を確定するときに移動対象を選び、Deflect を払う。Mageseeker Investigator と合わせて3枚を `full` にした（CR 355.4–355.12, 403, 809）。[Vendetta 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/vendetta-rules-faq-and-clarifications/)

### 分配ダメージと確定済み対象の追跡（2026-11-27）

- Alpha Strike の対象数は確定時の味方 Unit の Might を上限とする。解決時は、依然として合法な対象のうち、現在の Might で各1点以上を割り振れる最大数を残し、ダメージを同時に与える。発生源は選んだ Unit で、ダメージに連動する XP の能力は、軽減と死亡置換の後で実際に死亡した対象ごとに Chain に乗る（CR 355.14, 388–389, 418.6, 429.5）。[公式総合ルール](https://cmsassets.rgpub.io/sanity/files/dsfx7636/news_live/5c7946f7c3b8c6e0faff85ab6dadc6d2e721ea94.pdf#page=50)
- Repulse は Base へ動いた対象も数え、対象が Board を離れて別のオブジェクトになると数えなくなる。Alpha Strike の Master Yi の Signature 指定と Calm／Body の Power コストを印刷に合わせ、Master Yi の4種の Unit に Champion 指定を補った。2枚を `full` にした。[Unleashed 公式 FAQ](https://playriftbound.com/en-us/news/rules-and-releases/unleashed-rules-faq-and-clarifications/) [公式カード画像](https://cmsassets.rgpub.io/sanity/images/dsfx7636/game_data_live/154940caa774fd8219625cf051ddcb230ffc7f02-744x1039.png)

### M8a の実装の記録（2026-11-24）: Spiritforged 27 — 対象の選びを、選ぶ時点で絞る

- **あとの選びは、前の選びを見る**: `Choice.candidatesAfter` / `targetsOkAfter` / `targetTuplesAfter`。2 つ目の対象の候補は、1 つ目の対象を `slot 0` として読める（`Filter.sameAs (.slot 0)` など）。以前は、違反する組を選ぶと、何も起きなかった。いまは、遊べない（`targetsOk` が偽）。
- **直したカード**: Bonds of Strength（SFD-151）と Deathgrip（163）と Defiant Dance（196）は、同じユニットを 2 回選べない。Switcheroo（145）は、同じ Battlefield の別のユニットだけ。Temptation（129）は、別のユニットだけ。Angle Shot（011）は、ユニットと同じ持ち主の Equipment だけ（`Filter.sameController`）。
- **変わらないもの**: Mighty の判定（Show of Strength、Rumble、Jaull-Fish）がパッシブの Might 増加を読まないのは、`Select` が `Passive` より下の層にあるため（`mightNow` を呼ぶと、層が循環する）。直すには、層の組み替えが要る。Bellows Breath の 2 つ目と 3 つ目、Piercing Light の 2 つ目、Emperor's Divide は、解決のときに選ぶ（選びが解決のときなので、Deflect の追加支払いと「選んだとき」は働かない）。

### M8a の実装の記録（2026-11-24）: Spiritforged 28 — 「最大 1 体」の対象と、Power の割引

- **最大 1 体の対象**: `Quantity.upTo 1` の対象は、遊ぶときに選べる（`Choice.optional`）。選ばなくてもよいのは、そのあとの選びがすべて「最大 1 体」のときだけ。選ばなかった枠は、`Selector.eval` の `slot i` が、空の集まりを返す（何も起きない）。Piercing Light（SFD-023）の 2 つ目と、Bellows Breath（080）の 2 つ目と 3 つ目は、遊ぶときの選びになった。Deflect の追加支払いと「選んだとき」が働く。Bellows Breath の「同じ場所」は、1 つ目と同じ場所（`.at_ (.slot 0)`）で、ダメージを受けたユニットも選べる。
- **Irelia の Power の割引**: コストの、どの Power の記号を落としてもよい（`dropPowers`）。先頭の記号だけ、ではない。
- **残っている近似**: Mighty の判定（`Filter.mighty`、`Filter.might`）は、パッシブの Might 増加を読まない（`Select` が `Passive` の下の層）。Emperor's Divide は、Battlefield を選び、そこの味方を 1 体ずつ「しますか」と聞く。Rocket Barrage の choose one は、解決のときに選ぶ。Janna は、Reaction で Battlefield へ遊べない。Irelia の Energy の割引は、`effCost` の下限を見ない。

### M8a の実装の記録（2026-11-24）: Spiritforged 29 — 残っていた近似を、さらに直した

- **Irelia の割引**: Energy の割引は、コストがすでに持つ下限（Vex など。`costMinusMin` の下限）を下回らない（`GameState.cutFloor`、`Cost.cutOptions` の `floor`）。Power を落とす割引で、記号の並びだけが違う選択肢は、1 つにまとめる（`canonPower`）。
- **Rocket Barrage（SFD-077）の choose one**: 遊ぶときに、対象（ベースのユニット、または Gear）を選ぶことで、モードが決まる（`Filter.either`、`Filter.both`）。解決のときに選ぶ形をやめた。近似: Repeat の 2 回目に、別の選択をすることは、できない（同じ対象に 2 回働く）。
- **Janna（SFD-053）**: 自分が支配する Battlefield へ、Reaction の速さで遊べる（`playToBf [.controlled]`。Rengar と同じ仕組み）。
- **Mighty と Might の判定が、パッシブの Might 増加を読む**: `Env.passMight`（オブジェクトごとの、パッシブが足す Might の表）を、`Filter.might` / `Filter.mighty` / `Filter.lethal` が読む。表は `GameState.mightTable`（`Passive.lean`）で、効果を 1 手進めるとき（`Frames.lean` の `.run`）と、対象を選ぶとき（`targetsOk` / `targetTuples` の `pm`）と、費用の減額（`costCuts`）で、その時点の状態から作る。Mighty を数える Show of Strength、Jaull-Fish、Rumble が、Draven のような、パッシブで Might が増えるユニットを数える。パッシブ自身が選ぶ・数えるときは、パッシブなしの Might を読む（パッシブが互いに依存しないための、従来どおりの決め）。印刷されたパッシブの Might 変更がどのカードにもないときは、表は空で、計算しない（速さのため）。近似: 手札のカードを選ぶ・遊べるかの判定（`Play.lean` の `unitsPlayable` など、環境を持たない判定）は、表を渡さない。
- **残っている近似**: Emperor's Divide は、Battlefield を選び、そこの味方を 1 体ずつ「しますか」と聞く（「選んだとき」の誘発が、自分のユニットでは働かない）。

### M8a の実装の記録（2026-11-24）: Spiritforged 30 — Rocket Barrage の Repeat

- **Rocket Barrage（SFD-077）**: Repeat を払うと、2 回目の対象を、遊ぶときに選べる（`StaticMod.repeatChooses`。対象は 2 つで、2 つ目は最大 1 体）。2 回目は、`.paid` のときだけ働く。同じ効果を、同じ対象で 2 回行う仕組み（`resolveFrames`）は、この印のあるカードでは使わない。近似: Repeat を払っても、2 つ目を選ばなくてよい（何も起きない）。（Repeat を払わないと、2 つ目は選べない: Spiritforged 31。）
- **手札のカードを判定するときの Might の表**: 手札・Trash のカードは、パッシブの Might を持たない（盤上のものだけ）ので、表を渡さなくても同じ結果になる。近似ではない。
- **残っている違い**: Emperor's Divide は、Battlefield を選んだあと、味方を 1 体ずつ「しますか」と聞く。動く結果は、「任意の数を選んで動かす」と同じ。違うのは、自分のユニットが「選ばれた」ときの誘発（Irelia の払い戻しなど）が働かないこと。任意の数の対象を選ぶには、対象の選びを、可変の長さにする必要があり、証明の作り直しが大きい（このカード 1 枚のため、見送った）。

### M8a の実装の記録（2026-11-24）: Spiritforged 31 — 任意の数の対象、Repeat の選び

- **任意の数の対象**: `Quantity.upTo n`（n ≥ 2）の対象は、最後の選びとして、候補のうち何体でも選べる（`Choice.multi`）。選ぶ順は、ObjId の昇順だけが合法（同じ組を 1 度だけ選ぶ。`subseqs`、`Choice.sortedCands`）。選んだ対象は、スロット `i` から後ろに並び、`Selector.slotsFrom i` が全部を指す。選ばない（0 体）もよい。Emperor's Divide（SFD-043）は、Battlefield を選び、そこの味方を何体でも選んで、Base へ動かす（上限は 99 で、実際のユニットの数より大きい）。自分のユニットが選ばれたときの誘発（Irelia など）が働き、Deflect の追加支払いも求める。
- **Rocket Barrage の Repeat**: Repeat を払わないと、2 つ目の対象は選べない（`castable` が見る）。
- **Fae Dragon（SFD-101）と Azir, Sovereign（SFD-177）**: 「最大 4 体」「任意の数のトークン」は、誘発のときに、対象として選ぶ（`Choice.multi`）。1 体ずつ「しますか」と聞くのをやめた。Deflect の追加支払いと「選んだとき」が、働く。Azir は、すでにその Battlefield にいるトークンを、選べない（動かないので）。
- **Flash（OGS-011）**: 「最大 2 体」を、本物の選びにした（以前は、1 体目だけが動き、2 体目は無視されていた）。
- **性能の限界**: 任意の数の対象は、候補の部分集合を全部、手として列挙する（`subseqsUpTo`。上限 n 体までだけを作る）。上限が大きい Azir, Sovereign（99）は、味方のトークンが 20 体いると、約 100 万通りになる。実際の対戦では、トークンは 10 体未満と見て、見送った。

### M8a の実装の記録（2026-11-24）: Spiritforged 32 — 残っていた近似を、さらに直した

- **Azir, Ascendant（SFD-050）**: 付ける Equipment を、能力を使うときに 1 つ選ぶ（最大 1 体の対象）。複数付けることはない。
- **Purifier（SFD-183）**: 「Your Equipment each give [Assault]」は、付いている Equipment 1 つにつき Assault 1（`StaticMod.equipEach`、`passiveKws`）。
- **Fiora, Peerless（SFD-110）**: 倍にした Might は、戦闘の終わりまで（`Duration.thisCombat`、`EndPoint.combat`、`endCombatObj`）。ターンの終わりまでではない。
- **「選んだとき」**: 能力が選ぶ対象でも、誘発する（`Event.chosenByAbility`、`TriggerEvent.chosenAny`）。Irelia, Fervent、Spirit Wheel、Blade Dancer は、呪文でも能力でも働く。Jae Medarda（『呪文で選んだとき』）は、呪文だけ（`TriggerEvent.chosen`）。効果が唱える呪文（`castInline`、`Prim.play`）の対象は、まだ働かない（その対象は、プレイのときに選ばない）。
- **Card Sharp（SFD-081）**: 「For each opponent who did」は、Gold を作った相手の数だけ、Gold を作る（相手が 2 人以上のとき）。

### M8a の実装の記録（2026-11-24）: Spiritforged 33 — 解決のときの選びも「選んだとき」を出す

- 効果が解決している間に選ぶ対象（`Selector.one` の選び: 候補が 1 つなら自動で、2 つ以上ならプレイヤーが選ぶ）も、選んだプレイヤーの物なら、「選んだとき」の誘発を出す（`chosenAt`: 呪文の効果なら `Event.chosenBySpell`、能力なら `Event.chosenByAbility`）。Irelia, Fervent・Spirit Wheel・Blade Dancer（呪文でも能力でも）と、Jae Medarda（呪文だけ）が、読む。
- 効果が唱える呪文（`castInline`、`Prim.play`）は、対象の無い呪文（`noChoices`）だけなので、その呪文の選びは、そもそも無い。
- **変わらない限界**: 任意の数の対象の組は、全部を手として列挙する（手の一覧が、仕様のとおり、合法な手の全部であるため）。Azir, Sovereign は、組を作らず、トークン 1 体ずつ「しますか」と聞き、「はい」と答えた分に `Prim.choose`（「選んだとき」の出来事だけを出す命令）を行ってから動かす。手の数は、トークンの数に比例する。Emperor's Divide（Battlefield 上の味方）、Fae Dragon（最大 4）、Flash（最大 2）の組の数は、小さい。

### M8a の実装の記録（2026-11-24）: Spiritforged 34 — 近似の総点検と、直した分

この節は、これまでの「近似」の記述を、現在のコードと照らして、まだ当てはまるものを選んだ結果。古い節の「近似」は、多くが後で直っている（直した記録は、各節にある）。

- **直した**: Dunebreaker（手札の数に、自分を数えない）、Dropboarder（Gear 2 つ以上は、誘発するときにも見る）、Fae Porter（動かせる味方がいなければ、払わない）、Pickpocket（コストを印刷しない Gold も、Energy 0 として選べる）、Beast Below（敵がいなくても、味方 1 体は戻る）、Perched Grimwyrm（制圧した Battlefield だけ。hold したものは、含めない。`Filter.conqueredByMine`）、Yone（ダメージの対象を、誘発のときに選ぶ。Deflect の追加支払いが求められる）、Here to Help（遊べない Battlefield を、選べない）、`perTurn`（手札などへ移って、出し直したカードは、使った記録を引き継がない）。
- **まだ当てはまる近似**（点検の結果）:
  - Reaction のユニットは、Battlefield へ遊ぶ能力でしか、Chain に応じて遊べない（Base へ、Reaction で遊ぶ手が無い。Janna、Rengar）。
  - 解決のときに払う費用（Draven, Vanquisher、Guards!、Hard Bargain、Void Rush ほか）は、浮いている Rune Pool からだけ払う。Rune を exhaust して払う手が無い。
  - 追加の費用を解決のときに払う（Legion Quartermaster、Bard、Zaun Punk、Blade of the Ruined King）。Dauntless Vanguard、Rengar、Perched Grimwyrm の遊ぶ能力は、Chain に載り、印刷の費用を払う。
  - Hard Bargain の「その持ち主」は、相手とした（1 対 1 では同じ）。Jayce は、その場で Gear を遊ぶ。Arise! は、作った Sand Soldier でなく、exhausted の Sand Soldier を ready にする。Rek'Sai、Void Rush（呪文を遊ばない）、Not So Fast（呪文だけ）、Altar of Memories（底に置く = リサイクル）、Arcane Shift（その場で遊び直す）、Edge of Night（選ぶ対象が、「ここ」に限られない）。
  - Tianna は、Battlefield の得点だけを止める。Ruin Runner は、印刷されたパッシブだけを読む。Aphelios は、選んだモードを、また選べる（何も起きない）。Vex、Needlessly Large Yordle は、Energy だけを動かす。Draven, Audacious の「戦闘で死んだとき」は、どの戦闘でも真。`heldPoints` は、得点が禁止された Battlefield も数える。Hostile Takeover の誘発は、Ending フェーズの始まりに一度だけ集める。Guardian Angel、Soraka は、Cleanup での死と Temporary を救わない。Rell は、付けていない Equipment のうち、このターンに遊んだ全部を付ける。Temporal Portal を 2 回使っても、Repeat は 1 つ。Relentless Pursuit は、Equipment を付けない。Fire Below the Mountain の Add に、制限が無い。Lonely Poro は、解決のときに数える。Loyal Pup は、`combatStarted` で誘発する。

### M8a の実装の記録（2026-11-24）: Spiritforged 35 — Power の費用、Tianna、Draven

- **Power の費用の変化**: `StaticMod.costPower`（`GameState.adjustPower`）。Vex, Cheerless は、味方の呪文の Power を 1 つ減らし（どの記号でもよい。先頭から落とす）、敵の呪文に `[A]` を 1 つ足す。Needlessly Large Yordle は、hold で得点した点の数だけ、Calm の記号を減らす。
- **Tianna Crownguard**: 相手が、効果で得る点（`Prim.score`）も止める。以前は、Battlefield の得点だけ。
- **Draven, Audacious**: 「戦闘で死んだとき」は、Draven が死んだ場所の戦闘だけ（`Condition.inCombatHere`）。
- **直せなかった**: 攻撃と防御の誘発が起きる時（Showdown の後、戦闘ダメージの前）を、Showdown の始まりへ移す変更は、試して戻した（テストが、誘発を直接起こして確かめているので、本物の Showdown と二重になる）。Cleanup での死の置き換え（Guardian Angel、Soraka）は、Cleanup の終わりの証明（`cleanupMeasure`）の作り直しが要る。Aphelios の使用済みのモードを選べなくするには、選び（`eitherDo`）の合法手と仕様（`Spec/Legal`）を、状態で絞る必要がある。

### M8a の実装の記録（2026-11-24）: Spiritforged 36 — 解決のときの支払い、Rell、Poro

- **解決のときに払う費用は、Rune も使う**: `Prim.pay` と `Condition.canPay` は、浮いている Rune Pool が足りないとき、Base の Rune を使う（`GameState.runePlan`、`runeCover`）。足りない Energy の分だけ、Ready の Rune を exhaust し、足りない Power の分だけ、その領域の Rune を recycle する（`applyRunes`、`applyRune_safe`）。払えないとき（Rune も足りない）は、これまでどおり払わない。Draven, Vanquisher、Guards!、Hard Bargain、Void Rush、Fae Porter、Blade Dancer などが、相手が先に Energy を浮かせなくても、払える。テストの `fund` は、Rune を使えなくして、Pool の分だけを払える状態にする（`noRunes`）。
  - 近似: 使う Rune は、自動で選ぶ（払いに要る領域の Rune は、最後に exhaust する。recycle は、exhausted の Rune を先に使う）。プレイヤーは選べない。1 つの Rune を exhaust してから recycle することは、しない。カードを遊びながら払う費用（`playFree`、`playReduced`、`attachPaying`）は、まだ Pool からだけ払う。Lonely Poro の「一人きり」は、Cleanup が 1 体ずつ殺すので、同時に死ぬ味方がいると、順に依存する。
- **Rell（SFD-024）**: 遊んだ直後の Equipment だけを付ける（`Filter.playedLast`）。このターンに先に遊んだ、付いていない Equipment は付けない。
- **Relentless Pursuit（SFD-184）**: 動かしたユニットに、同じ持ち主の Equipment を付けてよい（最大 1 つ。選ぶのは遊ぶとき）。
- **Lonely Poro（SFD-036）**: 「一人きりで死んだ」は、死んだときに数える（`TurnEffect.diedAlone`、`noteAlone`）。能力が解決する前に、ほかのユニットが来ても、変わらない。
- **まだ**: 追加の費用を解決のときに払うこと（Legion Quartermaster ほか）、Reaction のユニットを Base へ遊ぶこと、Cleanup での死の置き換え、Aphelios の使用済みのモード、Hostile Takeover の誘発の集め方、Arcane Shift、Fire Below the Mountain の Add の制限、Temporal Portal（2 回で Repeat 1 つ。規則が不明）。

### M8a の実装の記録（2026-11-24）: Spiritforged 37 — 遊びながら払う費用も、Rune で払う

- `payByRunes`（Pool から払い、足りなければ Rune を使う）を、`Prim.pay` のほか、効果が遊ぶカードの費用（`playPaying`、`playReducedOne`）、Equipment を付ける費用（`applyAttachPaying`）、その場で唱える呪文の Power（`castInlineStep`）にも使う。以前は、どれも Pool からだけ払い、足りないと、何も起きなかった。近似: 使う Rune は、自動で選ぶ。

### M8a の実装の記録（2026-11-24）: Spiritforged 38 — Reaction のユニットは、Chain に応じて遊べる

- Reaction を持つユニットやギアは、Chain に応じて遊べる（`reactable`、`reactStep`）。呪文のように Chain に載らず、すぐに Base へ出て、遊んだときの誘発（Janna の「ここ」のヒールと追い出しなど）が Chain に載る。Battlefield へ遊ぶ能力（Rengar、Janna）は、これまでどおり。

### M8a の実装の記録（2026-11-24）: Spiritforged 39 — Arcane Shift、選べない分かれ道

- **Arcane Shift（SFD-200）**: ユニットを追放し（`Prim.banishReplay`）、その持ち主が、費用を無視して遊ぶ。新しいオブジェクトで、バフ・ダメージ・付いていた Equipment は無く、exhausted で Base に出る。トークンは、追放されて消える（遊ばない）。
- **選べない分かれ道**: 「条件だけの枝」（`.ifThen 条件 効果 .nop`）は、条件が偽のとき、選べない（`Effect.viable`、`eitherOk`。`Spec/Legal` と `legalFrameActions` が、同じ条件で絞る。どの枝も選べないときは、どれを選んでもよい）。Aphelios, Exalted の、このターンに選んだモードは、もう選べない。Angle Shot の「detach」は、同じユニットに付いているときだけ選べる。

### M8a の実装の記録（2026-11-24）: Spiritforged 40 — 攻撃と防御の誘発は、Showdown の始まりに起きる

- 攻撃する・防御する能力（`TriggerEvent.attack`、`defend`、`youDefend`）の出来事（`Event.combatStarted`）は、戦闘ダメージの前でなく、**Showdown の始まり**（Cleanup が Showdown を始めるとき。両陣営にユニットがいるとき）に出す。誘発は、Showdown の途中で Chain に載り、プレイヤーが呪文を唱える前に解決する。Fiora が倍になるのも、この時。Showdown が戦闘にならずに終わっても、誘発は、すでに起きている。
- テストの `fire` は、Main フェーズの `priority` フレームを外して動かす（その後の Cleanup が、新しい Showdown を始めて、出来事を二重にしないため）。`startCombatNow` は、出来事を自分で起こす。

### M8a の実装の記録（2026-11-24）: Spiritforged 41 — ユニットの、マナでない追加の費用

- カードが、追加の費用として、マナでない物を求めるときは、`CardDef.playExtra`（`PlayExtra`: ギアを手札へ戻す・ギアを kill する・Legend を exhaust する。必須かどうか）で書く。遊ぶときの対象に、その物を 1 つ選び（`playTargets`、`GameState.extraOk`）、遊ぶと同時に、費用を払う（`payExtra`、`applyExtra`）。払ったカードは、`paid` を覚え、`Condition.paid` が読める。必須の費用は、払えないと、遊べない。選べるのは、自分のギア（Legend は、ready のもの）だけ。
- Legion Quartermaster（ギアを戻す。必須）、Bard, Mercurial（Legend を exhaust する。任意。払ったときだけ、ユニットを空いた Battlefield へ動かす）、Zaun Punk（友軍のギアを kill する。任意。払ったときだけ、ギアを kill する）。払うタイミングが、解決のときから、遊ぶときへ変わった。
- **まだ**: Blade of the Ruined King の「Equip — Order、友軍のユニットを kill する」は、Equip の費用の一部だが、kill するユニットを解決のときに選ぶ。

### M8a の実装の記録（2026-11-24）: Spiritforged 42 — Blade of the Ruined King

- Equip の費用の「友軍のユニットを kill する」は、kill するユニットを、能力を使うとき（`activate` の対象の 2 つ目）に選ぶ。付ける先のユニットとは、別のユニット。kill は、能力が解決するときに行う（費用として、使うときに kill するのではない）。近似: 解決するまでは、そのユニットは生きている。
- **まだ**: Guardian Angel と Soraka が、Cleanup での死を救わないこと（Cleanup の終わりを示す測り方の作り直しが要る）。Fire Below the Mountain の Add の制限（Rune Pool の払い出しの作り直しが要る）。

### M8a の実装の記録（2026-11-24）: Spiritforged 43 — ギア専用のマナ

- **Fire Below the Mountain（SFD-189）**: Add した Power は、その回、ギアを遊ぶときと、ギアの能力にだけ使える。`ManaKind.gear`（Add して、`TurnEffect.gearMana` を、そのターンの記録に足す）。ギア以外（ユニット・呪文・ギア以外の能力・効果の中の支払い）の支払いは、記録した数（Pool の `any` を超えない。`GameState.restrictedNow`）の `any` を、残さなければならない（`GameState.spendFor`。`playable`、`castable`、`activatable`、`payNow` が使う）。
- **近似**: 制限は、Pool の `any` の数と、ターンの記録の数（Legend は 1 ターンに 1 回だけ使うので 1）の小さい方。ギアで使ったあとに、別の Add で `any` が増えると、増えた分も、制限を受ける（制限を受ける分が、使ったあとにも残る）。
- **まだ**: Guardian Angel と Soraka が、Cleanup での死を救わないこと（Cleanup の終わりを示す測り方の作り直しが要る）。

### M8a の実装の記録（2026-11-24）: Spiritforged 44 — Cleanup での死の身代わり

- **Guardian Angel（SFD-051）と Soraka（SFD-173）**: ダメージだけでなく、Cleanup で致死になった（Might が下がった）ユニットも、救う。`cleanupKill`（Battlefield.lean）が、Guardian Angel なら、Angel を殺して、ユニットを回復・疲労・Base へ戻す（`saveUnit`）。Soraka なら、Battlefield にいる弱いユニットを、同じように、救う。救えない場合（Battlefield 上でない、など）は、従来どおり殺す。
- **Cleanup が終わる証明**: 測りの先頭を、場にあるものの数から、`GameState.pot`（場にあるものの数＋Battlefield Zone にあるものの数）へ変えた。ユニットを Battlefield から Base へ戻すと `pot` が 1 下がり、殺すと下がるので、救っても、Cleanup は終わる（`sendHome_core` / `saveUnit_pot_lt` / `saveUnit_none_pot_lt` / `killObj_pot_lt`）。
- **まだ**: Blade of the Ruined King の「殺す」を、解決時に選ぶ件など、細かい点だけ。

### M8a の実装の記録（2026-11-24）: Spiritforged 45 — Blade of the Ruined King の kill は費用

- **Blade of the Ruined King（SFD-178）**: Equip の「友軍のユニットを kill する」を、費用として、能力を使うときに払う（`AbilityCost.killFriendly`、`payKill`）。選んだ物の最後が、死ぬユニットで、Chain に載せる前に死ぬ。解決のときは、装備するだけ。対象は、能力を使うときに選ぶ（装備するユニットと、死ぬユニット）。
- **証明**: `applyActivate_cases` に、費用の支払いの状態（`Safe`）を足した。手札と Chain は、`killObj_zone_other` で、そのままだと示す。
- **これで、記録していた近似は、すべて直した**。

### M8a の実装の記録（2026-11-24）: Spiritforged 46 — Edge of Night、Not So Fast、Arise!

- **Edge of Night（SFD-139）**: 遊んだときの誘発に、`condition := .fromHidden` を付けた。手札から遊んだときは、誘発せず、対象も聞かれない。
- **Not So Fast（SFD-045）**: 呪文だけでなく、味方のユニットかギアを選ぶ敵の能力も、打ち消せる（`Place.onChainAll`。打ち消された能力は、消える。`counterObj`）。
- **Arise!（SFD-198）**: 作った Sand Soldier のうち 2 体が、ready で出る（残りは exhausted）。以前は、前からいる exhausted の Sand Soldier を ready にしていた。

### M8a の実装の記録（2026-11-24）: Spiritforged 47 — Jayce、Hard Bargain、hold の点

- **Jayce（SFD-084）**: ギアを殺したあと、そのターンの間、手札から遊ぶ次のギア（Energy コストが 7 以下）は、Energy 0 で遊べる（`TurnEffect.nextGearFree`、`costCuts`）。以前は、その場で遊んでいた。Power は払う。ギアを 1 つ遊ぶと、使い切る。
- **Hard Bargain（SFD-136）**: 払う側は、打ち消される呪文の持ち主（`PlayerSel.controllerOf`）。以前は、すべての相手。
- **hold の点**: 得点が止められた（Tianna）Battlefield は、「hold で得た点」に数えない（`markScored`）。
- **Fire Below the Mountain**: ギア専用の印は、Add するとき、すでに使った分を、引く（`trimGear`）。
- **近似でないと確かめたもの**: Ruin Runner（「選べない」を与えるカードは、ほかに無い）。Altar of Memories（リサイクルは、山札の底へ置く）。Hostile Takeover（Ending フェーズの始まりより後に作った遅延誘発は、規則でも誘発しない）。
- **まだ**: Void Rush が、見たカードの呪文を遊べない（呪文は、対象を選んで、Chain に載せる遊び方が、効果の中から、まだできない）。Fire Below the Mountain の専用の Power を、ギアで使ったとき、残りの扱いが、厳密ではない（新しく Add した Power を、制限しない、ただし、残りは、制限したままにする）。Temporal Portal を 2 回使ったときの Repeat（規則が不明）。

### M8a の実装の記録（2026-11-24）: Spiritforged 48 — Void Rush の呪文、ギア専用 Power の残り

- **Void Rush（SFD-188）**: 見た呪文も、遊べる（`Prim.castPicked`、`castReducedStep`、`castPickedOne`）。遊べる対象の組が複数あれば、プレイヤーが選び、費用を 2 Energy 安く払って、呪文は Chain に載る（相手は応じられる）。対象が選べない呪文は、引く。
- **Fire Below the Mountain**: ギアを遊ぶとき、ギアの能力を使うときに使った Power は、ギア専用の印から先に引く（`gearSpent`、`preCost`）。使い残した Power は、ギア以外にも使える。
- **Temporal Portal**: 2 つ使ったときの Repeat は、規則の資料（`docs/rules-model.md` の 820）に、複数の Repeat の扱いが無いので、決められない（近似ではなく、規則が不明）。
- **小さな漏れ**: ギアの効果の中で払う費用（`Prim.pay`）で、ギア専用の Power を使ったときは、印を引かない。

### M8a の実装の記録（2026-11-24）: Spiritforged 49 — Repeat の重ね掛け、効果の中の支払い

- **Repeat は、重なる**（CR 820.1。Rift Watcher、RiftJudge の裁定）: Repeat は、1 つずつ別に、1 回だけ払える。払った数だけ、呪文の効果を、もう一度行う。Temporal Portal を 2 つ使えば、Repeat が 2 つで、両方払うと、3 回行う。印刷された Repeat に、Portal の Repeat を足しても、同じ（`playCostsOfK`、`Object.extraPaid`、`resolveFrames`）。払う費用は、追加の費用の、どの組み合わせでもよい。
- **ギアの効果の中の支払い**: ギア専用の Power は、`Prim.pay` など、ギアの効果の中の支払いでも、先に引く（`setPoolFor`）。
- **これで、ロードマップに記録していた近似は、残っていない**。確かめていない近似が見つかれば、その都度、直す。

### M8a の実装の記録（2026-11-24）: Spiritforged 50 — Repeat のやり直しで、対象を選び直す

- 効果をもう一度行うとき（Repeat）、対象を、もう一度選ぶ（CR 820.2）。2 回目からは、効果の前に、対象のひとつごと（1 つを選ぶもの）に `Effect.fillSlot` が入り、解決のときに、その場の状態から選び直す（`EffectDef.refills`、`executions`。選んだ物は `fillFromPick` で、スロットに入る）。最初の 1 回は、遊ぶときに選んだ対象のまま。数を選ぶ対象（up to N など）や、モードは、選び直さない。

### M8a の実装の記録（2026-11-24）: Spiritforged 51 — 近似の再点検（1）

ロードマップの近似を、現在のコードと照らし直した（読むだけの点検）。まだ当てはまっていたものを、順に直す。

- **Quick-Draw のギアは Reaction を持つ**: Long Sword、Sterak's Gage、Cloth Armor、Spinning Axe が、Chain に応じて遊べる（`reactSpell`）。
- **Add 能力を使うと、「能力を使った」出来事が起きる**: Prize of Progress が、Gold などの Add でも誘発する（`applyMana`）。
- **Rek'Sai, Swarm Queen**: 遊んだユニットは、その Battlefield に出る（`playReduced` に here を渡す。呪文は、`castReducedStep` が、遊び先に関わらず遊ぶ）。
- **Temporary のユニット**: 開始時に殺されるときも、身代わり（Guardian Angel、Soraka）が働く（`killAll` が `killOrSave`）。
- **Emperor of the Sands**: 「Equipment を遊んだ」を、Equipment だけで数える（`Amount.equipmentPlayed`）。
- **Drag Under**: 手札以外から遊ぶと、2 安い（Void Drone と同じ）。

### M8a の実装の記録（2026-11-24）: Spiritforged 52 — 近似の再点検（2）

- **Akshan, Mischievous**: 取ったギアの印を、取ったユニットの識別子にした（`Object.takenBy : Option ObjId`、`formerId`、`takerKey`）。同じカードの Akshan が、もう 1 体いても、その Akshan が場を離れたときに、返らない。
- **Kato the Arm**: ほかのユニットに、持っているキーワードを、すべて渡す（`Prim.giveKeywords`）。以前は、Deflect だけ。
- **Harpoon Squad**: 効果で Base へ動かされたときも、動いたことになる（`moveHome` が、動いた数と `standardMoved` を、記録する）。
- **トークンのユニット**: Forecaster の Vision が、Mech のトークンにも働く。Rally the Troops の後に出たトークンは、バフが付く（`buffNewTokens`）。
- **Soraka**: Base にいるユニットも、同じ場所なので、救う（`deathSaver`）。Cleanup で、Might が下がって致死になった、Base のユニットは、まだ救わない（`cleanupKill` は、Battlefield の上だけ）。
- **Fiora**: ユニットが Mighty になるのを、バフと装備だけでなく、Might が変わる、どの変化でも、見る（`Event.becameMighty`、`GameState.mightyEvents`。作業の 1 歩ごとに、前後の状態を比べる）。
- **Ezreal, Prodigy**: 追加の費用の「1 Energy か 1 Power 安く」を、どちらでも選べる（`extraAlts`）。追加の費用は、1 つずつ別に、選べる。

### M8a の実装の記録（2026-11-24）: Spiritforged 53 — Battlefield へ遊ぶのは、遊ぶこと

- **Battlefield へ遊ぶ**（Dauntless Vanguard、Rengar、Perched Grimwyrm、Miss Fortune、Origins の「空の Battlefield へ遊べる」）は、能力でなく、ふつうの「遊ぶ」操作になった。`playCard` の対象に、Battlefield を 1 つ選ぶ（`GameState.playBfOptions`、`bfPlayOk`、`placeAtBf`、`playable` の `dest`）。ユニットは、Chain に載らず、その場で、その Battlefield に出る。費用は、遊ぶ費用（軽減も効く）。Reaction を持つユニットは、Chain に応じても、遊べる（`reactable`、`reactStep` も、追加の費用と、遊ぶ先を、扱う）。
- 以前は、「手札から、印刷の費用を払い、能力として、Chain に載る」ものだった。軽減が効かず、相手が、その能力に応じられた。

### M8a の実装の記録（2026-11-24）: Spiritforged 54 — 「好きな量を払って、Add する」

- **Hextech Anomaly（SFD-083）と Ancient Henge（SFD-117）**は、Chain に載らない Add 能力（応じられない）になった。払う量と、払う Power の領域は、プレイヤーが選ぶ（`Action.manaAbility` に `pay` が付いた。`ManaKind.powerToEnergy`、`energyToPower`、`manaPays`、`powerBags`）。以前は、1 つずつ、最大 12 回、Chain 上で、順に聞いていた。Power を払うときの領域の選びは、`legalActions` に、全部の払い方が、並ぶ（Pool にある数と、`any` で足りる数まで）。

### M8a の実装の記録（2026-11-25）: Spiritforged 55 — The Zero Drive の Deathknell

- **The Zero Drive（SFD-090）**: 付いているユニットは、死んで、Trash へ行き、そのあとで、Zero Drive が、追放する（`Filter.banishedWithMe`）。以前は、死ぬ代わりに、すぐ Banishment へ行っていた（死んだことに、なっていなかった）。`GameState.banishedOnDeath` は、いつも偽（印は、`banishedWith` に、残る）。
- **Soraka（Cleanup、Base のユニット）**: Might が下がって致死になった、Base のユニットも、癒して、exhaust する（Base にいるので、Base へ戻すのは、何も変えない）。ダメージが付いているときだけ。付いていない（Might が 0 以下で致死）なら、死ぬ。Cleanup の測りの 2 番目に、「ダメージが付いているものの数」（`GameState.dmgC`）を足したので、癒すと、測りが下がり、Cleanup は終わる（`dmgC_heal`）。

### M8a の実装の記録（2026-11-25）: 近似の点検の結論

ロードマップに記録された Spiritforged の近似は、これですべて、直したか、近似でないと確かめたか、規則が定めていないものである。直したものは、Spiritforged 34 以降の各節にある（PR #198〜#211）。


### M9 の実装の記録（2026-11-25）: Unleashed — 225 枚が動く

目標は、Unleashed の 225 枚（トークン 8 種を含む）が、すべて `CardDef.runs` を満たすこと。**225 / 225 枚が動く**（`RiftboundTest/Cards.lean` の `#guard` で固定）。PR #212 で 157 枚、続く PR で残りの 68 枚。

- **エンジンに足したもの（前半）**: Ambush（Battlefield へ、Reaction として遊ぶ）、Backline（最後に割り当てる）、XP を使う（`Prim.spendXP`）、XP を得た印（`TurnEffect.gainedXP`）、Beginning Phase に死んだ印（`diedInBeginning`）、Hide の出来事（`TriggerEvent.hide`）、2 枚の入れ替え（`Prim.swapTop`、Predict 2）、Battlefield の Conquer と Hold を 1 回多く（`triggersExtra .conquer/.hold .here`）、ダメージを倍に（`TurnEffect.doubleDamage`）、死ぬ代わりに追放（`TurnEffect.banishInstead`）、次のユニットにバフ（`nextUnitBuffed`）、疲れて入る Gear（`StaticMod.entersExhausted`）、ほかのユニットに戦闘ダメージを与えさせない（`noCombatDamageFor`）、「選べない」を、ほかのユニットにも（`cant (all ...) .beChosen`）。
- **エンジンに足したもの（後半）**: Battlefield トークン（`Prim.addBattlefield`、`replaceBattlefield`、`restoreBattlefield`、`Object.replaces`。Baron Pit、Brush）、トークンが別のカードのコピーになる（`Prim.becomeCopy`、Reflection）、トークンをもう 1 つ（`cloneToken`）、動かした場所にトークン（`createAtPrev`）、タグを得る（`gainTag`、`Object.tagsGained`）、ゾーンの札をまとめて動かす（`moveAll`、`banishWith`、`Place.inBanishment`）、Trash から遊ぶ能力（`AbilityCost.fromTrash`）、呪文の Repeat を与える（`StaticMod.grantRepeat`）、Elder Dragon（`anyDamageKills`）、Maduli（`Object.cantReady`）、ユニットに付いた Equipment の、ターン終了の能力（`timedTriggers`）、Arachnoid Horror（`playToBfAll`、`Filter.enemyAlone`）、LeBlanc（`ignoreKeyword .temporary`）、相手が得点する・ホールドする（`opponentScores`、`opponentHolds`）、自分の効果が敵ユニットを動かす（`Event.movedByEffect`）、カードを引いた（`Event.drew`、`drewCard`）、呪文だけを遊べなくする（`opponentsNoSpells`）、次ターンまでユニットの費用を増やす（`unitsCostMore`）、Showdown の条件（`inShowdown`、`showdownNow`）、PlayExtra `killPet`（Stalking Wolf）。
- **フィルターと条件**: `Filter.mightLtOf`、`choosesOnly`、`myUnitsHere`、`enemyAlone`、`sharesGainedTag`、`Condition.hasHidden`、`spentOnSpell`、`beginningPhase`、`iControlHere`、`drewCards`。条件に Might の合計を書ける（`Amount.evalS0` が、バフと装備と、パッシブの分を足した Might を読む）。Battlefield の能力は、そのユニットの持ち主のために働く（`watchersOf`）。
- **近似として残したこと**: 呪文の追加の費用（「味方のユニットを殺す」など）は、解決のときに払う（選ぶユニットは、遊ぶときに選ぶ）。Poppy, Defender of the Meek は、XP が 3 以上あれば、自動で 3 払って 3 安くなる（払わない選択が無い）。Atakhan は、追加の費用（ユニットを殺す）と、それによる軽減が無い。Stalking Wolf は、殺したユニットの Battlefield へ遊べない。Conscription は、3 Might 以下を選ぶなら XP は要らず、それより大きいユニットを選んだときだけ、解決のときに 5 XP を払う。Safety Inspector の XP は、解決のときに払う。相手に選ばせる選択（Call to Battle、Shard of Undoing、Safety Inspector、Bone Skewer）は、`eachPlayer` で、そのプレイヤーの側から選ぶ（Bone Skewer は、相手が自分のユニットを選ぶ）。Insightful Investigator は、手札を見せない（選ぶだけ）。Hwei は、捨てる札の種類を、モードとして選ぶ。Dancing Grenade は、最大 3 回まで（相手側から）。Death from Below は、1 回だけ、もう 1 体を、Power 1 で殺す。Undying Loyalty は、費用の軽減が無い。Tactical Retreat は、死んだあとで戻る（Unlicensed Armory と同じ）。Ashe, Focused の返す効果は、Ashe が場にいるあいだだけ。Gardens of Becoming は、Battlefield の能力（ユニットを exhaust して 1 XP）。Lilting Lullaby は、呪文を打ち消されたプレイヤーでなく、使ったプレイヤーの相手が、呪文を遊べなくなる。Scorn of the Moon は、Showdown のときだけ使える Add 能力（Energy の使い道の制限ではない）。Hextech Gauntlets と Bashful Bloom の費用の軽減は、軽減ごとの別々の能力。Curtain Call と Square Up の Repeat は、解決のときに払う（Square Up は捨てる）。Star Spring、Zilean は、1 ターンに 1 回（プレイヤーごとでなく）。The List は、全部のタグの中から名前を選ぶ。

### M9 の点検の記録（2026-11-25）: Unleashed の近似と食い違い

225 枚すべてを、5 つの読み取り専用のレビュー（UNL-001〜045、046〜090、091〜135、136〜180、181〜219 とトークン）で、印刷の文と実装を突き合わせた。指摘は 101 行（1 枚で 2 行のものと、複数枚で 1 行のものがある）。**通常のプレイで結果が違う（A）が 22 行、まれなときだけ違う（B）が 約 40 行、ほぼ影響なし（C）が残り**。実装が、レビューの指摘どおりか、コードを読んで確かめてから直した。

- **直したもの（IR だけ）**: Heroic Charge（2 つ目の対象を選べず、唱えられなかった）、Loyal Poro（条件が逆。仲間がいないときに引いていた）、Sacrifice（channel が 2 つになっていた）、Cursed Sarcophagus（Energy を払わずに出していた）、Flurry of Feathers（Chain に呪文が無いと、Bird のモードを唱えられなかった）、Back Off（Hidden から出しても引いていた）、Yuumi（このターンでなく戦闘の間だけ）、Fresh Beans（戦闘のない Showdown でも）、Isolate（動かせなかったときも引いていた）、Keeper's Verdict（持ち主でなく、使った人が上か下かを選んでいた）、Pridestalker と Valley of Idols（トークンのユニットで誘発しなかった）、Ivern（引いたカードの ID が変わるのでバフが働かなかった。手札のペットの数で判定する）、Hwei（持っていない種類を選べて、ボーナスだけ得た）。
- **直したもの（エンジン）**:
  - `Prim.pickSel?` と `withSel` に `banishWith` と `replaceBattlefield` を足した（Ashe, Focused と Green Father が、何もしなかった）。
  - **Hidden から出したユニットは、伏せた Battlefield に出る**（CR 811.1.d。Marai と Evelynn が、動かなかった）。`CardDef.hiddenPlay` が `playTo .self (.locationOf .self)` を使い、`locationOf` は伏せたカードの場所を `hiddenAt` で答える。Hidden の既存のテスト 3 本が、Base に出る前提だったので直した。
  - **ユニットとギアが Base にいるときの「ここ」は、その Base**（`GameState.baseHere`、`placeObjs .here`、`applyCreate .here`。Frisky Hunter、Lord Broadmane、Megatusk）。Sona と Eager Apprentice が、「ここ」を「Battlefield にいる」の代わりに使っていたので、`.matches .self .onBattlefield` に直した。
  - ユニット自身の「Base へ動けない」（Determined Sentry。`homeForbiddenFor`。Standard Move と `moveHome`）。
  - `Prim.counterToHand`（Abandon：打ち消した呪文が、持ち主の手札へ戻る）。呪文を打ち消せる相手を、敵だけから、誰でもに直した。
  - 効果で与えた「死んだとき」の能力（`grantsAbility`）は、死んだカードの新しい ID にも付く。誘発するのは、与えた人（Deadly Flourish は、敵のユニットが死んでも、Gold は与えた人が出す。Tactical Retreat）。
  - Equipment の Level の条件つき Might（`equipBonus`。Soul Sword の Level 3）。
- **残したもの（エンジンの機能が要る。優先順）**:
  1. **追加の費用**（A）: Atakhan、Poppy, Defender、Safety Inspector、Conscription、Heedless Resurrection、Sacrifice。呪文には、追加の費用を遊ぶときに払う仕組み（`PlayExtra`）が無い（`extraOk` が呪文を除いている）。ユニットの「費用が下がる」も、払ったかどうかに連動しない。
  2. **Showdown の中の Action / Reaction**（A）: Shadow は、能力が丸ごと使えない。Action と Reaction の呪文も、Showdown の中では唱えられない（roadmap L1336）。
  3. **死ぬ代わりに**（A）: Tactical Retreat、Altar of Blood は、死んでから戻る（「死んだとき」の誘発と、Deathknell が余分に働き、トークンが消える）。`ReplaceEvent.die` を置換として解釈する必要がある。
  4. 呪文のプレイを選ぶ・相手の手札から選ぶ（Bone Skewer、Call to Battle ほか）、Battlefield を選んで出す（Thrill of the Hunt）、手札へ離れるときの元の Battlefield（Ripper's Bay）。
  5. 条件が、誘発した呪文を見ない（`spentOnSpell`：Revna、Virtuoso、Forgotten Library）、`excessAtLeast` が、その Conquer を生んだ戦闘に結びつかない（Piltover Enforcer、Hextech Gauntlets、Trapping Grounds）、`Filter.hasKeyword` が、与えられたキーワードを読まない（Petal Pixie、Smoke and Mirrors、Bashful Bloom、Black Flame Altar）、Level の条件つきの能力を `blocksChoice` が読まない（Master Yi, Unstoppable の Level 16）。
- **近似として、残してよいもの（C）**: 解決のときに選ぶ対象（Deflect の支払いが働かない）、手札を見せない、Dancing Grenade、Death from Below、Scorn of the Moon、Star Spring、Zilean、Gardens of Becoming、Curtain Call と Square Up の Repeat、`returnToHand` が「引く」の誘発を起こさない、など。

### M9 の追加の費用（2026-11-25）: 遊ぶときに払う

点検（上の節）の次の一手として、追加の費用を、解決のときでなく、遊ぶときに払うようにした。

- **仕組み**: `PlayExtra` に `killUnit`（味方のユニットを殺す）と `spendXP n`（XP を払う。費用を払う相手は、プレイヤーの Legend）を足した。ユニットとギアは、これまでと同じ流れ（`playTargets` → `extraOk` → `payExtra0`）で、遊ぶときに払い、`paid` が付く。**呪文**は、`castPay`（`castStep` と `applyPlayCard` の中）で、唱えるときに払う。費用の対象は、呪文が選ぶ **1 つ目の対象**（カードの最初の `targetOf` が、費用の対象を表す。`castable` の検査はそのまま使える）。払うと、Chain の上の呪文の 1 つ目の対象は、死んだカードの新しい ID（Trash）になるので、効果は、そのユニットの費用を読める。呪文の `paid` は Repeat のための印なので、立てない。
- **直したカード**: Heedless Resurrection、Sacrifice（唱えるときに殺す。唱える前から、味方のユニットが無いと唱えられない）、Safety Inspector（3 XP を払うかを、遊ぶときに選ぶ。払うと、自分は殺さない）。相手は、費用を払ったあとの状態に応答する。
- **まだのもの**: Poppy, Defender of the Meek（XP で、Energy が 3 安くなる）、Atakhan（殺したユニットの費用ぶん、安くなる）、Conscription（XP を払ったか、で選べる対象が変わる）。どれも、**費用や選べる対象が、選んだ追加の費用で変わる**。`playable` と `applyPlay` が、まだ選んだ対象（`ts`）を受け取らないので、そこに `ts` を通し（`playable`、`paysForXT`、`paidExtra`、`applyPlay`）、費用を減らす関数（`cutOptionsOf` の拡張）を足す必要がある。`Undying Loyalty` は、さらに、Trash の対象を選べない（`placeObjs .inTrash` が未対応）。

### M9 の追加の費用（続き、2026-11-25）: 費用が変わる 3 枚

選んだ追加の費用で、費用や選べる対象が変わるカードも、遊ぶときに払うようにした。

- **選んだ対象を、遊べるかの検査に通す**: `playable` が、選んだ対象（`ts`）を受け取り（省略すると空）、`paysForXT` で払える費用を調べる。`GameState.extraCutOf` が、選んだ追加の費用が、費用から引くもの（Energy と Power の数）を返し、`cutOptionsOf` がそれを使う。`PlayOk`、`bfPlayOk`、`reactable` は、`ts` を渡す。`CardDef.paidCut`（`PaidCut.energy n` / `.killed`）が、カードの印刷を表す。`paidExtra` は、減った費用を払っただけなら、Accelerate を払ったことにしない（`extraAltCosts`）。
- **Poppy, Defender of the Meek**: 3 XP を払うかを、遊ぶときに選ぶ。払うと、費用が Energy 3 安い。払わなければ、全額で、XP はそのまま。Ambush で遊ぶときは、Battlefield を選ぶので、XP は払えない（近似）。
- **Atakhan**: 味方のユニットを殺すかを、遊ぶときに選ぶ。殺すと、そのユニットの Energy と Power の数だけ安い。
- **Conscription**: 3 Might 以下の敵ユニットは、そのまま選べる。それより大きい敵ユニットは、XP が 5 以上あるときだけ選べ、**唱えるときに 5 XP を払う**（`Filter.xpAtLeast`、`PlayExtra.spendXPOver`。XP を払うかは、選ぶ対象で決まる。小さい対象を選ぶのに払う理由は、無い）。
- **Undying Loyalty** は、まだ。選ぶ対象が Trash にあり、`placeObjs .inTrash` が未対応。

### M9 の Showdown の中の Action と Reaction（2026-11-25）

Showdown の中で、Focus を持つプレイヤーは、pass だけでなく、次のことができる（CR 347-348、806、813）。

- **呪文**: Action を持つ呪文（`showdownable`：`reactable` か、`castable` で `actionSpell`）、Reaction を持つ呪文とユニット（Ambush を含む）。Action も Reaction も持たない呪文は、Showdown の中では唱えられない。
- **能力**: Action か Reaction の速さの起動型能力（`activatableSD`：Chain が空で、`showdownSpeed`）。
- **資源**: Rune の能力と、Add の能力（Chain の上の項目への応答と同じ）。
- **仕組み**: `applyFrame0` に、`.showdown` の `playCard`、`activate`、`runeAbility`、`manaAbility` を足した。唱えたり、使ったりすると、`chainPass q 0 :: showdown bf q 0 :: rest` になる（Chain が解決すると、Showdown に戻り、pass の数は 0 から数え直す）。`legalFrameActions` と `LegalFrame` は、`legalShowdownPlays`、`legalShowdownActivates` を使う。証明は、`Sound`、`Step`、`Hands`、`Progress`、`Setup`、`ClockRun` に、`chainPass` の場合と同じ形で、4 つずつの場合を足した。`Clock.legal_timeCalled` と `Draw.legal_declareDraw` は、`LegalFrame` の場合が増え、`split` が重くなったので、`maxHeartbeats` を上げた。
- **直したカード**: Shadow（Action の能力が、防御側の Showdown の中で、攻撃している敵を Stun する）。ほかのセットで、これまで Showdown の中で使えなかった Action と Reaction のカードも、使えるようになった。
- **近似として残したこと**: Chain が解決したあと、Focus は、使ったプレイヤーに戻り、pass の数は 0 から数え直す（規則の Focus の移り方は、確かめていない）。通常の速さの呪文と能力は、Showdown の中では使えない（Action と Reaction だけ）。Showdown の中のプレイは、Chain の上の項目への応答と同じく、カードの `reactable` の判定をそのまま使う。

### M9 の「死ぬ代わりに」（2026-11-25）: Tactical Retreat

- **仕組み**: `TurnEffect.saveOnce`（そのユニットに付ける印）と `saveUsed`（救ったことの印）を足した。`deathSaver` は、`saveOnce` があって、まだ `saveUsed` が無いユニットを、Soraka と同じ形（`some none`）で救う。救うと、ユニットは、ダメージが消え、exhausted になり、Base に戻る。`saveUnit` は、救ったあとに `saveUsed` を残す（`saveUnitCore` に、印を足した）。Cleanup の Base で治す枝にも、同じ印を足した。終了性の証明は、`pot` を `saveUnitCore` について示し、`saveUnit` の `pot` は、印を足しても変わらない、で通した。
- **直したカード**: Tactical Retreat（ユニットは、死なない。Deathknell は働かず、トークンも消えず、同じユニットのまま。2 回目に死ぬときは、死ぬ）。
- **まだのもの**: Altar of Blood（「3 Power を払って、治して、exhaust して、Recall する」。払うかを選ぶので、死ぬ瞬間の純粋な関数（`deathSaver`）では扱えない）。いまは、死んでから、3 Power を払って戻る近似のまま。
