# 自動処理の停止（I12）: どこまで言えるか

`step` は、答えを受け取ったあと、作業フレーム（work frame）を 1 つずつ処理して、次の決定フレーム（choice / chance）に着くまで進める（`advance`）。この処理が**必ず止まる**ことが、I12（[roadmap.md](roadmap.md)）である。止まらなければ、`step` は fuel（今は 100 歩）が尽きて `fuelExhausted` を返す。

I12 のうち、エンジン上で連続する Cleanup と Expiration、初期手札を引く作業の停止を証明した。対局中のドローと誘発キューの上限、効果の制御構文の有限性を示し、即時 Add は観測まで含めた実際のエンジンで元の処理に戻ることを証明した。登録済みのカードでは、Might のしきい値を越えても即時 Add が積まれず、通常の誘発キューは連続する自動処理で有限回のうちに処理される。通常の優先権での Pass は、終了フェイズの即時 Add と Expiration を処理してから、次のターンの Main を含めて次の入力か空のスタックまで進む。最後のマリガンから最初のターンに入る場合も、実際の `step` が有限の fuel で成功する。`AdvancePrefix.finish` は、その確認を済ませた選択で停止することを示す。証明の範囲は §3 に示す。

## 1. 今ある確認（証明ではない）

- 実際のゲームで測った: 乱数の種 60 個 × 答えの方針 4 通り = 240 ゲーム（すべて終わりまで）、答え 19,567 個。**1 つの答えのあとの作業フレームは、最大 19 歩、平均 2.94 歩**。fuel は 100 なので、約 5 倍の余裕がある（Core Rules のデモのデッキ。`riftbound-live` を通した）。
- `RiftboundTest/Fuel.lean`: デモのゲームを終わりまで遊び、fuel 切れとエンジンの内部エラーが出ないことを確かめる（Core Rules 12 種、時計つき 12 種、Limited 6 種）。ドライバーは、どちらのエラーでも止まるので、終わりまで遊べれば、どの答えも fuel に収まっている。
- **この確認が言えないこと**: デッキや局面が別なら、別の数になりうる。カードの効果は IR で書かれ、`repeatN` のように、実行時に決まる回数だけ繰り返すものがある。

## 2. 止まる理由（見込み）と、証明に要るもの

作業フレームの一覧と、それぞれが何を積むか（`Rules/Frames.lean` の `microStep0`）:

| フレーム | 積むもの | 止まる理由（見込み） | 証明に要るもの |
|---|---|---|---|
| `setupHands`、`beginTurn`、`phase` | 次の段階のフレーム（有限） | 段階は決まった順で、1 ターンに一度ずつ | 小さい。測度は「残りの段階の数」 |
| `draw p n` | `draw p (n-1)`、または Burn Out の `chanceBurnOut`（決定フレーム） | `n` が減る。Main Deck が空なら決定フレームで止まる | 小さい。測度は `n` |
| `resolveChain`、`finishSpell` | `run`、`finishSpell`、`cleanup` | Chain の項目が 1 つ減る | 中。Chain の長さ |
| `run p src env todo` | 効果 1 つ分の実行と、残りの `run` | 効果の木が小さくなる（`seq`・`ifThen`・`bind` は、自分を消して、部分の効果を積む） | **中〜大。`repeatN` と `forEach` が、部分の効果を実行時の回数だけ複製するので、効果の大きさの和では測れない。複製を許す整列（多重集合の順序）の測度が要る** |
| `cleanup` | 状態を 1 つ直して、また `cleanup`（仕上げは、勝者の宣言、Showdown、何もしない） | 直すたびに、下の測度が減る | **大。下の 3 を見る** |
| `expireTurn` | 必要なら `cleanup` と再度の `expireTurn` | リセットが再度の Expiration の条件を消し、Cleanup の観測でも条件は復活しない | Cleanup と Expiration が連続する区間を証明済み（§3f） |
| `triggers pend` | 先頭を Chain に置いて `triggers`（残り）、または選択（決定フレーム） | `pend` が短くなる。必要に応じて `chainPass` で応答を待つ | 新たな観測で処理が変わるまでの上限は証明済み（§3d） |
| `combatDamage`、`combatResolve` | 割り当て（決定フレーム）、`cleanup` | Combat は 1 回ごとに終わる | 中 |

通常の誘発型能力は Chain に置かれ、解決前に `chainPass` でプレイヤーの応答を待つ。一定の条件を満たす Add は、CR 430.2 に従い `PendTrigger.immediateAddFrame` が `run` を直接積む。停止の証明では、この Add が実行できる資源処理も数える必要がある。

## 3. 最も重い部分: Cleanup

`cleanupFrame` の通常の反復では、`cleanupStep` が `some` を返すたびに状態を直し、`cleanup` をまた積む。1 回の直しは、次のどれか（`Rules/Battlefield.lean`）: Board の外にあるトークンの消滅、離れた Equipment の取り外し、致死ダメージの Unit の撃破、支配する Unit を失った Battlefield の Control の解除、古い Contested の解除、新しい Contested。

止まることを示す測度の案（字引き順）:

1. 全オブジェクトの数（トークンの消滅で減る）
2. 場にある（`inPlay`）オブジェクトの数（撃破で減る）
3. 取り外すべき Equipment の数
4. Control を失った Battlefield の数
5. 古い Contested の数
6. 新しく Contested になる Battlefield の数

前の項目が減らないとき、次の項目が減る。後ろの項目を増やすことがあっても、前の項目が減っていれば足りる（例: Control の解除で、新しい Contested が増えうる）。

**証明の障害**（実際に見つけたもの）:

- `killObj` は `sendObj` を通り、`moveObj` が失敗すると、**何も変えずに成功を返す**（`sendObj` の `none` の腕は、状態をそのまま返す）。そのとき `cleanupStep` は同じ状態を返し、`cleanup` は**永久に繰り返す**。`moveObj` が失敗するのは、移動先が不正（持ち主がプレイヤーの数以上）のときなどで、`WF` と `OwnerOk` が成り立つ状態では起きない。つまり、**証明には、`WF` と `OwnerOk` から「撃破が必ず場の数を減らす」を示す補題が要る**。`Reachable` の不変条件（I1、I3）をそのまま使える。
- 撃破で、Unit に付いていた Equipment が残ることがあり、取り外し（3）が増える。字引き順で、(2) が減っていれば足りる。

### I12a の結果（証明済み）

- **定理**: `cleanup_terminates` と `cleanup_no_infinite_run` は、`WF` な状態からの `cleanupStep` の反復が有限であることを示す。公理は標準の 3 つだけ。**ほかの前提は無い**。
- Radiance の同時撃破や入れ子の死亡置換は `cleanupFrame` でまとめて処理する。状態の不変条件は `cleanupResolveDeathGroup_safe` で示す。実際の作業フレームでの停止証明の範囲は §3e に示す。
- **測度**: 上の 6 つを字引き順にした組（`GameState.cleanupMeasure`、順序は `MeasLt`）。**6 つの歩み（トークンの消滅、Equipment の取り外し、撃破、Control の解除、古い Contested の解除、新しい Contested）の、どれもが測度を真に減らす**ことを、1 つずつ示した。
- **撃破が場の数を減らすのに要る条件**: 撃破される Unit の持ち主が、ゲームのプレイヤーであること。なければ、持ち主の Trash がゲームのゾーンでなく、移動が失敗して、状態が変わらないまま Cleanup が繰り返す。**遊べるどのゲームでも、どの物体の持ち主もプレイヤーである**が、これを不変条件として全部の腕で証明するには、フレームに入るプレイヤー（優先権、`run`、誘発の controller）の妥当性まで通す必要があり、大きい。そこで、**`GameState.lethal`（致死ダメージ: CR 142.4.b）に「持ち主がプレイヤーである」を足した**。遊べるゲームでは、動きは変わらない。持ち主がプレイヤーでない物体は、致死ダメージとは数えず、Cleanup は撃破しない（そういう物体は、遊べるゲームには存在しない）。

### 3a. 初期手札を引く作業の上限（証明済み）

[`advance_setupHands_bound`](../Riftbound/Invariant/SetupDrawBound.lean) は、セットアップ中の `setupHands` から、最初のマリガンまたは Burn Out の偶然の選択までに必要な fuel が高々 `5 * 席数 + 1` であることを示す。セットアップ中は誘発を積まない。最初の 1 歩でドローを積み、各席につきカード 4 枚と残り 0 枚のフレームを処理するため、2 席なら 11 歩、4 席なら 21 歩で足りる。山札から引けない場合も同じ上限で偶然の選択に着く。

### 3b. 対局中のドローの上限（証明済み）

[`advance_draw_bound`](../Riftbound/Invariant/DrawWork.lean) は、残り `n` 枚のドローについて、元の処理に戻るか、Burn Out の選択に着くか、イベント処理が最初に状態を変えた直後に着くまで、高々 `n + 1` ステップであることを示す。一枚以上引いたバッチでは、残り0枚のフレームがまとめて引いたイベントを出す。`AdvancePrefix` が消費した fuel とイベントの順序を追跡するので、その時点から残りの fuel で続行できる。

### 3c. 効果の組み合わせと即時 Add

- [`RawWorkPrefix.observe`](../Riftbound/Invariant/WorkPrefix.lean) は、ルールディスパッチャー `microStep0` の有限な遷移列を、イベント処理を含めた `advance` に結び付ける。予定した後続処理に達するか、イベント処理が予定した状態を変えた直後に達するかを示す。後者の後続処理には別の上限が必要になる。
- [`ControlWork.lean`](../Riftbound/Invariant/ControlWork.lean) は、順次実行、条件分岐、変数束縛、`repeatN`、`forEach`、`eachPlayer` の有限性を、本体となる効果の有限性から導く。繰り返し回数と対象の数は実行時の値を使う。どの効果も、先行する効果が更新した状態で実行する。XP の獲得と資源を加える効果にも適用できる。
- [`insertDetectedTriggers_addWork`](../Riftbound/Invariant/AddWork.lean) は、イベント処理が先に積む即時 Add の全件について、使用記録と効果のルール処理が有限であることを示す。その後には通常の誘発と元の処理が続く。
- [`RiftboundCards.advance_detectedTriggers`](../RiftboundCards/MightRead.lean) は、登録済みカードで、検出済みの即時 Add を実際の `advance` ですべて解決し、先頭に通常の誘発キューがあれば続けて処理することを示す。使用回数の記録と資源の追加では、新たな準備・疲労や Might の観測が起きない。任意ドメインの Power を追加するときに整理する Gear 専用の記録、条件分岐、実行できずスキップしたイベントも扱う。
- 終了フェイズで実際に検出した即時 Add と、再開する Cleanup・Expiration を合わせた停止は §3n に示す。

### 3d. 通常の誘発キューと再度の観測（上限と条件を証明済み）

- [`advance_triggers_bound`](../Riftbound/Invariant/TriggerWork.lean) は、待機中の誘発が `n` 件のとき、高々 `n + 1` ステップで元の処理、Chain の応答、誘発の順序などを選ぶ決定、または新たな観測によって状態が変わった直後のいずれかに達することを示す。自動で Chain に置く場合、残りのキューが短くなる。
- [`workStep_triggers_observed`](../Riftbound/Invariant/TriggerObservation.lean) は、構造が整った状態での通常の誘発の一手を、観測まで含めて特定する。盤上の物体を消耗させず、この一手から新たに待機する誘発は Might がしきい値を越えた観測から生じる。誘発が追加される場合も、観測そのものではプレイ履歴、ターン中の記録、勝敗は変わらない。
- [`advance_detectedTriggers`](../Riftbound/Invariant/TriggerWork.lean) は、検出された即時 Add を順に処理し、続いて先頭に来た通常の誘発キューを処理する。元の解決処理が通常の誘発より前にある場合はそこに戻る。Might の観測から生じた誘発も、同じ証明で扱える。観測で途中の状態が変わった場合、そこまでに発行したイベントは当初の処理列の先頭部分と一致する。

### 3e. エンジン上の Cleanup の連続処理（停止を証明済み）

[`advance_cleanup_work`](../Riftbound/Invariant/CleanupWork.lean) は、先頭が Cleanup の状態から、イベント処理を含む実際の `workStep` を有限回適用すると、先頭のフレームが Cleanup 以外になるか、フレームがなくなることを示す。同時撃破と入れ子の死亡置換も対象に含む。

通常の Cleanup は盤面の測度を減らし、後続の Cleanup に戻るときは待機中の Cleanup の個数を減らす。イベント処理がターンの記録を更新したり、Cleanup の後ろに通常の誘発を追加したりしても、停止証明は成り立つ。

[`cleanupResolveDeathGroup_cleanupChange`](../Riftbound/Invariant/CleanupDeath.lean) は、実際の撃破グループ全体で `pot` が増えず、盤上から物体が除かれた場合は厳密に減ることを示す。入れ子の死亡置換を適用するときも、すでに盤上から離れた物体の旧 ID は復活しない。

[`cleanupResolveDeathGroup_decreases`](../Riftbound/Invariant/CleanupDeathDamage.lean) は、`pot` が変わらない場合も、最初の致死対象のダメージが消え、グループ全体でダメージを受けた物体の数が減ることを示す。このとき盤外のトークン数は同じなので、Cleanup の測度は必ず減る。Cleanup を出た後、他の作業フレームも経て次の決定に至る全体の証明は I12c〜d に残っている。

### 3f. 終了フェイズの Cleanup と Expiration

[`advance_ending_expiration`](../Riftbound/Invariant/ExpirationWork.lean) は、終了フェイズの開始から、実際の `workStep` で進む Cleanup と Expiration が有限回で区切れることを示す。途中から同じ処理を追うときは `advance_expiration_work` を使える。観測で積まれた誘発キューや即時 Add が先頭に来た場合は、その処理に移る時点までを証明する。

リセットはダメージ・スタン・期限付き効果・資源プール・ターン中の記録を、再度の Expiration が不要な状態にする。そこから Cleanup が進んでも、対象になる状態を作り直すことはない。Might のしきい値を越えたときなどの観測も、ターン中の記録を復活させない。測度は Expiration フレームの個数の2倍に、リセットが必要なら1を足した値を先に比べ、それが同じときは Cleanup の測度を使う。

### 3g. Might のしきい値と即時 Add

[`db_mightTriggersAreOrdinary`](../RiftboundCards/MightObservation.lean) は、登録済みのカードとトークンすべてについて、Might を監視する能力番号から即時 Add が解決されないことを `decide` で確かめる。Gear がユニットになって能力番号が変わる場合も、解決側が参照する元の定義と照合する。

[`workStep_expireTurn_mightOrdinary` と `workStep_triggers_mightOrdinary`](../Riftbound/Invariant/MightObservation.lean) は、条件を満たすデータベースで、実際の Expiration と通常の誘発確定が Might の観測で積む作業が通常の誘発キューに限られることを示す。通常の誘発確定から再び観測が起きるかは §3j で扱う。

### 3h. 通常の誘発を Chain に置くときの Might

[`putTrigger_automatic_mightInputs`](../Riftbound/Invariant/TriggerFinalization.lean) は、対象を選ばず通常の誘発を確定するときに、常在型能力の発生源と効果文、印刷・期限付きの Might、バフと装備の加算値が保たれることを示す。効果文には装備でコピーしたものも含む。[`putTrigger_automatic_mightWatches`](../Riftbound/Invariant/TriggerFinalization.lean) は、ターン中に付与された能力も含め、監視中のしきい値の一覧が保たれることを示す。

[`advance_triggers_noMightWatches`](../Riftbound/Invariant/TriggerWork.lean) は、監視中のしきい値が空の局面で、実際の `advance` が誘発キューの件数＋1ステップ以内に次の判断か元の処理へ進むことを示す。監視がある局面でも、各 Unit の Might が変わらなければ新しい誘発は生じない。

静的カード検査を通る試験用定義で、Chain 上の項目数を Might に加える常在型能力を置くと、通常の誘発を Chain に置くだけで Might が4から5に増え、さらに誘発が1件積まれた。監視するしきい値自体は同じなので、この経路を扱うには常在型能力が何を参照するかも考える必要がある。

### 3i. Might を変える常在型能力の読み取り

[`db_mightReads`](../RiftboundCards/MightRead.lean) は、登録済みのカードとトークンで Might や Tank・Assault・Shield に関わる常在型能力の条件と参照式が、証明対象の式に収まることを `decide` で確かめる。印刷された定義とユニット化した Gear の定義を照合する。

[`triggersStep_activeMightMods`](../Riftbound/Invariant/MightRead.lean) は、検査を通ったデータベースでは、通常の誘発を処理しても既存のオブジェクトで有効な Might 関連の常在型補正の一覧が変わらないことを示す。装備でコピーした効果文、Trash の枚数を数える式、今の戦闘で攻撃側や防御側にいるかの判定を含む。

### 3j. 登録済みカードの通常の誘発キュー

[`workStep_triggers_sameMight`](../Riftbound/Invariant/MightValue.lean) は、補正の値と下限、装備から着用者への補正、Tank・Assault・Shield を合わせ、通常の誘発処理で盤上の最終的な Might が保たれることを示す。検査は着用者への補正に使う対象の参照と、着用者と同じ場所にある別の Unit に付与するキーワードも対象にする。

[`RiftboundCards.advance_triggers`](../RiftboundCards/MightRead.lean) は、Might のしきい値を監視する能力が場にいても、登録済みカードで実際の `advance` が誘発キューの件数＋1ステップ以内に判断を求めるか、元の処理へ進むことを保証する。全体の停止証明では、Cleanup が積んだ即時 Add など、別の種類の作業へ移った後も追う必要がある。

### 3k. 通常の優先権で Pass した後の終了フェイズ

[`RiftboundCards.step_priority_pass_ending`](../RiftboundCards/MightRead.lean) は、通常の優先権だけがスタックにある状態での合法な Pass から、実際の `step` を追う。終了フェイズの Cleanup と Expiration を処理した後、通常の誘発が待っていれば、元の作業を再開する前にプレイヤー判断へ到達する。4人戦の投了で空の Battlefield が加わったカードデータでも成り立つ。

通常の誘発キュー以外に進む場合の到達先は、空のスタック、プレイヤー判断、次のターンの開始、イベントが積んだ即時 Add のいずれかになる。即時 Add の場合は、そのフレームを生成した誘発と、生成時に参照したゲーム状態を定理に残す。どの到達先でも、使った手数とイベントの順序を保って残りの `advance` につながる。スタックが空になるか、通常の優先権に必要な確認を終えたプレイヤー判断に着いた場合は、そこで使った手数で `step` が成功する。

### 3l. 終了フェイズから次のターンへの移行

[`RiftboundCards.step_priority_pass_to_awaken`](../RiftboundCards/MightRead.lean) は、合法な Pass から続けて、終了フェイズの先頭処理が `beginTurn` に達した場合に次のターンへの移行を追う。時計が決着を要求すれば `beginTurn` の1ステップで試合が終わる。プレイを続ける場合はターン番号と手番を更新し、Awaken から Main の優先権までのフレームを用意する。

ターンをまたいで Might のしきい値を越え、通常の誘発が積まれたときは、Awaken の処理より先にプレイヤー判断へ到達する。終了フェイズ中に積まれた即時 Add は、ターンをまたぐ前に §3n の証明で解決する。Awaken に到達した場合は §3m につながる。

### 3m. Awaken と準備完了による誘発

[`db_awakenTriggersAreOrdinary`](../RiftboundCards/MightObservation.lean) は、Awaken 開始と準備完了の誘発が、解決時に即時 Add を参照しないことを `decide` で確かめる。印刷された定義、ユニット化した Gear、装備からコピーした効果文、付与された能力が検出する誘発を、実際の能力番号で照合する。Might がしきい値を越えた場合も、§3g の検査と組み合わせて通常のキューに限られることを示した。

[`RiftboundCards.step_priority_pass_through_awaken`](../RiftboundCards/MightRead.lean) は、合法な Pass から実際の Awaken を処理し、誘発があれば次のプレイヤー判断、なければ元の Beginning 以下のフレームに到達することを示す。Beginning に進む場合は、ゲーム状態の構造とカードデータが保たれる。終了フェイズ中の即時 Add はそこで解決する。時間切れによる決着や途中のプレイヤー判断に至る場合も、発行したイベントと残りの fuel を保つ。

### 3n. 即時 Add を含む終了フェイズの停止

[`RiftboundCards.step_priority_pass_ending_with_adds`](../RiftboundCards/MightRead.lean) は、通常の優先権での合法な Pass から、終了フェイズの開始時と Cleanup 中に観測された即時 Add を実際のエンジンで解決する。Add が追加した資源を消去する Expiration も含めて、次のプレイヤー判断、空のスタック、次のターンの開始のいずれかに有限回で着く。通常の誘発で Chain が開く場合も、その判断点までの手数とイベントを保持する。

続く Cleanup と Expiration は、残っている Expiration の数、Cleanup が使う盤面の測度、期限切れにする状態の有無、残っている Cleanup の数を、この順に比較する。盤面を変える Cleanup は即時 Add が資源を増やしても盤面の測度が減る。盤面を変えない Cleanup は自身のフレームを消費する。Expiration は自身のフレームを消費するか、次の Expiration を積む前に期限切れにする状態を消去する。この証明を §3l と §3m の定理にも接続した。

### 3o. Beginning から次の決定点まで

[`advance_beginning_to_preparedDecision`](../Riftbound/Invariant/TurnPhaseWork.lean) は、Beginning の Temporary と死亡置換、追加ドロー、Hold、Channel、Draw、Main を、実際の作業順に追う。Hold の得点がドローに置き換わる場合、Draw を飛ばす効果、山札切れの Burn Out、Main の Cleanup が始める Showdown も含む。通常の誘発は残っている Cleanup やドローの後ろに積み、入力が必要になった時点で `advance` が状態とイベント列を返す。

[`RiftboundCards.step_priority_pass_to_preparedDecision`](../RiftboundCards/MightRead.lean) は、登録済みカードで、通常の優先権だけが残った状態から合法な Pass を行うと、有限の fuel で実際の `step` が成功することを示す。Ending と Expiration、次のターンの時計判定と Awaken から Main までを扱い、その途中で入力を求める場合も含む。4人戦で投了後の空の Battlefield がデータベースに加わる場合にも適用できる。

### 3p. Chain の最後の Pass と先頭項目の解決

最後の Pass で先頭項目を解決するときは、エンジンがその局面で生成する Run の命令列を検査する。対応する命令列なら、実際の効果と即時 Add、項目を Chain から移す処理、必要な Recycle、Cleanup を処理する。効果でプレイされ、宣言の確定を待つ Spell も §3r の処理を経て次の入力に進む。[RiftboundCards.MightRead](../RiftboundCards/MightRead.lean)

検査は条件分岐、繰り返し、変数束縛、対象やプレイヤーごとに行う処理、ドロー、資源処理、ダメージ（§3t）などを扱う。プレイヤー判断が途中に入る場合はそこで止まり、通常の誘発は残っている解決フレームの後ろに積む。個別の選択付きで Repeat した Spell の実行は §3q に示す。効果でプレイされた Spell の宣言確定は §3r に示す。未対応の効果命令には引き続き証明が必要である。

`step_chainPass_last_checked_to_preparedDecision` と `step_chainAnswer_checked_to_preparedDecision` は、検査を通る最後の Pass と効果への回答について、実際の `step` が有限の fuel で次の入力か空のスタックまで進み、状態とイベント列を返すことを示す。通常の優先権に戻る場合は、後続に Combat の参加者を更新するフレームがない条件で、入力を返す準備が積む Cleanup も含める。[RiftboundCards.MightRead](../RiftboundCards/MightRead.lean)

### 3q. 個別の対象やモードを記録した Repeat

[`RiftboundCards.step_chainPass_last_repeated`](../RiftboundCards/MightRead.lean) は、記録された実行を順に処理する。各実行を始める時点でカードの定義とモードを読み直し、元の対象をその時点の盤面で検査する。残せる対象の組が複数あるならプレイヤー判断に進む。ドローと即時 Add、Chain の終了処理は §3o と §3p の証明につながる。

`step_chainPass_last_repeated_to_preparedDecision` は、登録カードで Repeat の各実行が途中の入力まで処理できる場合、§3p と同じ条件で `step` の成功を示す。後続 Spell の宣言確定と優先権を返す準備も含む。対応外の命令列に達した場合は、その実行の手前までを証明し、対象とモード、そこまでの状態とイベントを保持する。対象を選ぶ効果、捨て札、複数の選択肢を出す効果も、実行がプレイヤー判断に達するところまで検査できる。[RiftboundCards.MightRead](../RiftboundCards/MightRead.lean)

### 3r. 効果でプレイされた保留 Spell の宣言確定

[`advance_limited_finalization`](../Riftbound/Invariant/LimitedSpellWork.lean) は、確定候補を生成し、対象や支払いに選択があればプレイヤー判断まで進む。合法な候補が一つなら自動処理を続け、宣言を確定して Chain の優先権へ移る場合、死亡置換の判断を求める場合、取り消して元のゾーンへ戻す場合を扱う。複数の保留 Spell が続く場合は、Chain の項目数と宣言確定の段階を順に比較する。取り消しに成功して次の Spell に移るたび、Chain の項目数が減る。即時 Add でゾーンの内容は変わらないため、観測を挟んでもこの減少は保たれる。

最後の Pass と Repeat の証明は、後続の保留 Spell をこの処理へ渡す。宣言確定から元の入力へ戻る場合も、必要に応じて §3p の Cleanup を経て状態とイベント列を返す。

### 3s. Showdown の最後の Pass とダメージ割り当ての確定

`step_showdownPass_last_to_preparedDecision` と `step_assignDone_to_preparedDecision` は、実際の `step` が有限の fuel で次の入力か空のスタックまで進み、状態とイベント列を返すことを示す。前者は Combat のダメージ置換順や割り当ての選択、割り当て不要の Combat、Combat がない場合の支配確定を扱う。後者はもう一方の割り当て、致死ダメージで生じる死亡置換の選択、ダメージ適用からリコール・戦闘結果・支配確定・Cleanup までを扱う。[CombatWork.lean](../Riftbound/Invariant/CombatWork.lean)

継続スタックには、通常の移動で残る Cleanup を含められる。通常の誘発は残る解決フレームの後ろに積み、即時 Add は観測時に実行する。ダメージ置換などの入力が出た場合はそこで止まる。通常の優先権に戻る場合は、後続に Combat の参加者を更新するフレームがない条件で、優先権を返す準備が積む Cleanup も扱う。登録カード用の定理は4人戦の投了後も使え、fuel を増やしても状態とイベント列は一致する。[RiftboundCards/MightRead.lean](../RiftboundCards/MightRead.lean)

`combatAnswerWorkSupported` は、Combat 中の回答が積む命令列と、その後に残る Combat の段階を確認する。ダメージ直後、リコール後、支配確定後の Cleanup から再開でき、途中で生じた誘発や追加の判断も処理順どおりに扱う。検査を通った合法な回答は、上と同じ優先権の条件で、有限の fuel で状態とイベント列を返す。[CombatWork.lean](../Riftbound/Invariant/CombatWork.lean)

### 3t. Spell と能力によるダメージ

`Effect.ObservedFinite.resolveDamage` は、ダメージの処理を「残りの対象別ダメージ件数、処理中の1件に残る置換数」の順に比較する。置換が一つしかなければ適用して先へ進み、複数の異なる置換や死亡置換があれば入力を待つ。通常の直接ダメージ、相互ダメージと振り分けも、実際のイベント観測を経て Run の続きか次の入力に進む。[DamageWork.lean](../Riftbound/Invariant/DamageWork.lean)

Chain の検査はこれらの命令と、一時的な Might などの付与、ターン中の効果の記録を扱う。Combat で死亡置換を求めるダメージも同じ定理を使う。毎回の Run で実際の盤面を参照し、選択やイベントの発生順を保持する。[RunWork.lean](../Riftbound/Invariant/RunWork.lean)

### 3u. Chain の効果に対する回答

`chainAnswerWorkSupported` は、任意効果の承諾・辞退、効果の分岐、対象選択に答えたとき、実際に積まれる Run 命令列を調べる。現在の項目を終えるフレームと、その後の入力または空のスタックを確認する。その前で待つ通常の誘発キューも扱う。[ChainAnswerWork.lean](../Riftbound/Invariant/ChainAnswerWork.lean)

検査を通った合法手は、回答とイベント観測を行い、選ばれた処理から次の決定点か試合終了に進む。配分やダメージ置換、死亡置換の回答を扱い、対象選択のイベントを含む実際のイベント列を保つ。登録カード用の定理は、4人戦の投了後を含め、fuel を増やしても結果が一致することを示す。[RiftboundCards/MightRead.lean](../RiftboundCards/MightRead.lean)

### 3v. 誘発の確定と保留された支払いの再開

`step_prepareTrigger_to_preparedDecision`、`step_triggerAdd_to_preparedDecision`、`step_cancelTriggerFunding_to_preparedDecision` は、支払いの準備、Add の選択、取り消しに対し、実際の `step` が有限の fuel で次の入力とイベント列を返すことを示す。誘発の確定は、現在の選択を支払って Chain に置く場合、見送る場合、確定前に死亡置換を求める場合を扱う。継続が入力待ちか空なら、残る通常の誘発も有限回で処理する。[TriggerAnswerWork.lean](../Riftbound/Invariant/TriggerAnswerWork.lean)

`triggerCostAnswerWorkSupported` は、置換への回答が積む命令列と保留された誘発の宣言を確認する。検査を通る合法手は回答を記録し、宣言を現在の状態でもう一度検査する。引き続き合法なら宣言を再開し、別の死亡置換が必要ならその入力に進む。合法でなくなった場合は元の誘発の選択へ戻る。回答時に生じた通常の誘発が先に入力を求める場合も扱う。[RiftboundCards/MightRead.lean](../RiftboundCards/MightRead.lean)

確定や再開で通常の優先権に戻るときは、必要な Cleanup を済ませ、そのイベントも順番どおりに含める。通常の優先権の後ろに Combat の参加者を更新するフレームがないことを仮定する。[TriggerAnswerWork.lean](../Riftbound/Invariant/TriggerAnswerWork.lean)

### 3w. カードのプレイ、能力起動、Recycle の支払い

通常の優先権、Chain、Showdown、チームの招待で合法なカードのプレイや能力の起動を宣言すると、実際の `step` が有限の fuel で次の入力か空のスタックに着く。起動コストに Trash からの Recycle が含まれる場合は、対象や戻し順を決める入力まで追える。支払いの完了時に起動イベントを発行し、そこから生じた誘発も処理順どおりに扱う。通常の優先権の後ろに Combat の参加者を更新するフレームがないことを仮定する。[PlayDeclarationWork.lean](../Riftbound/Invariant/PlayDeclarationWork.lean) [RecyclePaymentWork.lean](../Riftbound/Invariant/RecyclePaymentWork.lean)

死亡置換に答えた後は、最初に宣言したプレイや起動を現在の状態で再検査する。合法ならその宣言を再開し、合法性を失っていれば元の入力に戻る。そのとき通常の優先権の準備が Cleanup を積む場合も処理する。`playCostAnswerWorkSupported` が回答で生成された Run を検査する。入力待ちに直接戻る対象選択や Recycle の順番の抽選は `decisionRunAnswerWorkSupported` が扱う。Chain の項目を完了する抽選は Chain 用の検査で扱う。[RiftboundCards/MightRead.lean](../RiftboundCards/MightRead.lean)

### 3x. 通常移動、グループ移動、戦場の選択

合法な通常移動とグループ移動の確定は、移動イベントを観測してから Cleanup を進める。調整と死亡処理を済ませ、誘発の入力、Showdown、通常の優先権、または空のスタックまで進む。グループ移動の宣言、Unit の選択、取り消し、複数の戦場で待つ Showdown の選択も、有限の fuel で実際の `step` が状態とイベント列を返すところまで示した。[MovementWork.lean](../Riftbound/Invariant/MovementWork.lean) [MightRead.lean](../RiftboundCards/MightRead.lean)

通常の優先権に戻る場合は、後続のフレームに Combat の参加者を更新するものがないことを仮定する。通常の優先権一つに戻る場合はこの条件を満たす。取り消し時に盤面処理が残っていれば、優先権を返す準備で積んだ Cleanup も処理する。[ObservedCleanupWork.lean](../Riftbound/Invariant/ObservedCleanupWork.lean)

`cleanupAnswerWorkSupported` は、死亡置換などの回答が積む Run と、それに続く Cleanup を検査する。検査を通る合法手は、選んだ処理と Cleanup、残る通常の誘発を経て、実際の `step` で次の入力か空のスタックに着く。通常の優先権に戻る場合は、後ろに Combat の参加者を更新するフレームがないことを仮定する。[RiftboundCards/MightRead.lean](../RiftboundCards/MightRead.lean)

### 3y. 基本 Rune と即時 Add の起動

`step_resourceActivation_to_preparedDecision` は、基本 Rune と即時 Add の合法な起動について、実際の `step` が有限の fuel で次の入力か空のスタックに着くことを示す。Chain、Showdown、チーム招待、効果の解決中の任意の支払いも対象に含む。通常の優先権での即時 Add は、イベントを観測してから Cleanup を終える。通常の優先権の後ろに Combat の参加者を更新するフレームがないことを仮定する。[ResourceDecisionWork.lean](../Riftbound/Invariant/ResourceDecisionWork.lean) [MightRead.lean](../RiftboundCards/MightRead.lean)

Add が資源を増やす量は、支払い後の残高に空のプールから計算した加算量を足す形で表せる。Energy と Power をまとめて加える場合も、各指示が増やす量を合計する。[ResourceDecisionWork.lean](../Riftbound/Invariant/ResourceDecisionWork.lean)

### 3z. カードの閲覧、公開、名前や種別の選択

手札の公開とデッキ上部の閲覧・公開は、イベントを観測してから内側の効果を進める。内側の効果が完了したときは、元の効果が使っていた参照先に戻る。公開されたデッキ上部を引く場合と Recycle する場合も証明の対象に含む。[DisclosureWork.lean](../Riftbound/Invariant/DisclosureWork.lean)

Predict は、カードを残すか Recycle するかを選ぶ入力と、必要な場合に Recycle の順番を抽選する入力まで追える。Predict の最終回答、カード名の指定、カード種別の推測は、実際に生成される効果と後続の処理を検査し、対応する Chain、Cleanup、通常の判断へ戻るまで追える。追加の fuel でも到達状態とイベント列は一致する。[ChainAnswerWork.lean](../Riftbound/Invariant/ChainAnswerWork.lean) [MovementWork.lean](../Riftbound/Invariant/MovementWork.lean)

`predictAnswerWaits` を通る Predict の回答と、`decisionRunAnswerWorkSupported` を通る効果の回答では、実際の `step` が有限の fuel で次の入力か空のスタックとイベント列を返す。回答に続く命令列や誘発を処理し、通常の優先権に戻る際は必要な Cleanup を済ませる。通常の優先権の後ろに Combat の参加者を更新するフレームがないことを仮定する。[ChainAnswerWork.lean](../Riftbound/Invariant/ChainAnswerWork.lean) [MightRead.lean](../RiftboundCards/MightRead.lean)

### 3aa. War の投了と入力先の切り替え

`concessionWorkSupported` は、War の投了で席と盤面上のオブジェクトを処理した直後の作業列を検査する。残り一席で試合が終わるとき、セットアップの入力や通常の判断に戻るとき、手番プレイヤーが投了して次のターンに進むときを扱う。手番を移す場合は Cleanup、Expiration、時計の判定、次のターンの各フェイズを通常の Pass と同じ証明で追う。観測や誘発が先に入力を求める場合も含み、追加の fuel で到達状態とイベント列は変わらない。[ConcessionWork.lean](../Riftbound/Invariant/ConcessionWork.lean)

Showdown の途中の Pass は次の参加者の判断に進む。2 対 2 の招待はチームメイトに判断を渡し、辞退は待っていた判断へ戻る。Combat の割り当てで Unit を選んだ場合は、同じ席で割り当ての入力を続ける。[DecisionHandoffs.lean](../Riftbound/Invariant/DecisionHandoffs.lean)

### 3ab. マリガンの選択と引き直し

合法な手札を脇に置くと、同じ席のマリガンの入力に進む。1枚以上を脇に置いて確定すると、引き直す枚数に1を足した作業ステップ以内に、Recycle の順序を決めるか、デッキが尽きた場合の Burn Out の決定点に着く。[DecisionHandoffs.lean](../Riftbound/Invariant/DecisionHandoffs.lean) [SetupDrawBound.lean](../Riftbound/Invariant/SetupDrawBound.lean)

手札を変えずに確定する場合と、脇に置いたカードを戻す順序を決める場合は、次の席の入力へ進む。最後の席では最初のターンを始め、Awaken から Main までを追う。どちらの場合も、実際の `step` が有限の fuel で成功し、次の入力を待つ状態か空のスタックと、そこまでのイベント列を返す。セットアップ中の投了で戦場トークンが追加されたカード定義にも適用できる。[SetupDrawBound.lean](../Riftbound/Invariant/SetupDrawBound.lean) [MightRead.lean](../RiftboundCards/MightRead.lean)

`advance_beginTurn_through_awaken` は、Beginning に入る前に時計で試合が終わった場合や通常の誘発で入力を待つ場合に、`advance` が追加の Cleanup を挟まず成功することも示す。Beginning まで進んだ場合は、そこまでのイベント列とカード定義を保った状態を返す。通常の誘発キューが空でないか、すでに Chain が開いているときは、元の継続が通常の優先権でも、誘発の処理は先に別の入力を求める。[ExpirationWork.lean](../Riftbound/Invariant/ExpirationWork.lean) [TriggerWork.lean](../Riftbound/Invariant/TriggerWork.lean)

### 3ac. セットアップのシャッフル、戦場、手番順

セットアップの合法なシャッフルと戦場の抽選は、残っているセットアップ入力へ作業ステップなしで進む。参加者が残っている状態で合法な手番順を確定すると、参加席数を `n` として `5n + 1` 作業ステップ以内に、最初のマリガンか、山札が尽きた場合の Burn Out の入力に着く。4席が参加していれば上限は21で、離脱した席のドローは数えない。いずれも実際の `step` に対する定理である。[SetupDrawBound.lean](../Riftbound/Invariant/SetupDrawBound.lean)

### 3ad. 最後の Cleanup から通常の優先権へ

盤面が Cleanup の不動点に達していて、残りが通常の優先権一つで Showdown を開かない場合、`advance` は1ステップで優先権を返す。連動ダメージの終了通知は履歴を更新する。登録カードで使う読み取り条件の範囲では、その更新で致死判定や勝利に必要な点数が変わらず、Cleanup の不動点を保つ。[ObservedCleanupWork.lean](../Riftbound/Invariant/ObservedCleanupWork.lean)

`advance_main_to_preparedDecision` は、標準の Main の開始時点から、実際の `advance` がイベント列を返して成功するだけの fuel が存在することを示す。開始時に盤面処理が残っていても、Cleanup と即時 Add を経て、確認済みの通常の優先権、Showdown、誘発などの入力、または試合終了で止まる。Main の直後に盤面が整い、追加の処理が発生しない場合には、開始イベントを保ったまま2ステップで優先権に着く。[TurnPhaseWork.lean](../Riftbound/Invariant/TurnPhaseWork.lean)

### 3ae. Burn Out の抽選と得点先の選択

`step_burnOutAnswer_checked_to_preparedDecision` は、Trash を山札へ戻す順番を記録した抽選と、1点を得る相手を選ぶ回答を扱う。投了で選べる相手が変わった場合も、実際の `applyFrame0` が残す処理を検査する。検査を通る合法手では、残りのドロー、対応する効果命令、Cleanup、Chain や Combat の終了処理を経て、次の入力待ちか空のスタックまで有限の fuel で進む。Beginning の追加ドローや Hold のドローで Burn Out した場合は、残るターンの段階を通常どおり進める。通常の優先権に戻る経路で後続スタックを検査する場合は、Combat の参加者を更新するフレームがないことを仮定する。[BurnOutWork.lean](../Riftbound/Invariant/BurnOutWork.lean) [TurnPhaseWork.lean](../Riftbound/Invariant/TurnPhaseWork.lean)

### 3af. 制限時間のコール

入力待ちでの合法な `timeCalled` は、そのターンを基準に制限時間を記録し、有限の fuel で次の入力待ちか空のスタックに進む。処理を終えた状態にも同じ制限時間が残る。通常の優先権の後ろに Combat の参加者を更新するフレームがないことを仮定する。[DecisionHandoffs.lean](../Riftbound/Invariant/DecisionHandoffs.lean)

### 3ag. ジャッジの引き分け宣言

`step_declareDraw_terminal` は、合法な引き分け宣言が任意の fuel で引き分けを返し、残る入力と作業を空にすることを示す。スタックを空にした結果として Might の計算が変わる場合でも、終局後に誘発を積まない。[Draw.lean](../Riftbound/Invariant/Draw.lean)

### 3ah. 制限時間とサドンデスの終局を記録する

通常のターン境界で制限時間による勝敗が決まると、`advanceWithDisclosures_beginTurn_clock` は1ステップで終局し、それまでのイベントとカード開示をそのまま返す。サドンデスで合法な Burn Out の得点先を選ぶと、`stepWithDisclosures_burnOutTarget_suddenDeath` は任意の fuel で得点した側の勝利を返し、残っていたドローを取り消す。記録には1点の加算だけが加わり、カードの開示はない。[BeginTurnWork.lean](../Riftbound/Invariant/BeginTurnWork.lean) [Clock.lean](../Riftbound/Invariant/Clock.lean)

### 3ai. 効果による得点と勝利

効果命令列の停止検査は `score` と `win` を扱う。どちらも1ステップで処理し、観測処理で終局が確定した場合は残りの命令へ進まない。サドンデスの得点と、2対2で効果がチームに勝利を与える場合に、後続のドローやカード開示がないことをテストで確認する。[RunWorkCore.lean](../Riftbound/Invariant/RunWorkCore.lean) [RunWork.lean](../Riftbound/Invariant/RunWork.lean)

### 3aj. Ready、Exhaust、Buff、Stun

停止検査は選択済みの対象への効果に加え、解決中に対象を1つ選ぶ場合も扱う。候補がなければ効果を飛ばし、1つなら対象を確定して効果を実行する。複数なら誰も選ばれていない状態で次の入力を待ち、合法な回答の後に対象へ効果を適用する。それぞれ、誘発の観測を含めて次の入力か残りの命令まで有限に進む。[RunWorkCore.lean](../Riftbound/Invariant/RunWorkCore.lean) [ChainAnswerWork.lean](../Riftbound/Invariant/ChainAnswerWork.lean)

### 3ak. 手札、Banishment、山札の一番上への移動

手札へ戻す、Banish する、山札の一番上に置く効果も、解決中の対象選択を含めて停止検査の対象にした。移動のイベントから装着置換の追加処理が生じないことを示し、誘発の観測は通常どおり行う。カード現物の保存、移動先、Banish を行った席、イベントの順序は再生経路で確認する。[RunWorkCore.lean](../Riftbound/Invariant/RunWorkCore.lean)

### 3al. ターン中に残る効果、Empower、伏せ札

ターン中に残る効果の記録と伏せ札への移動、および Empower の付与・消費と Buff の消費を停止検査で扱う。テストでは Empower の上限、各イベントの順序、伏せたカードの現物と戦場、席ごとの見え方を確認する。[RunWorkCore.lean](../Riftbound/Invariant/RunWorkCore.lean) [Chain.lean](../RiftboundTest/Chain.lean)

### 3am. 効果の解決中に払うコスト

Banish、Disempower、Exhaust、Buff の消費を前段とする効果は、前段が実際に成立した場合にだけ後続の命令を実行する。エンジンが解決中の対象選択を提示した場合はその入力で止まる。Rune Pool からの支払いは、可能な内訳が1つなら支払い後に進み、複数なら内訳の選択を待つ。選択を受け取った後は支払いを再確認する。後続の命令が停止検査を通るときに、これらの処理を証明の対象にした。[RunWorkCore.lean](../Riftbound/Invariant/RunWorkCore.lean)

### 3an. 効果による Unit や Gear のプレイの確定

効果によるプレイの計画、支払い候補の提示、プレイの確定を停止検査で扱う。追加コストの死亡置換を選ぶ局面では入力を待ち、成功した場合は場に出たカードの新しい識別子を同じ Run の後続命令に渡す。Base に置く指定と、Banishment から再プレイする計画も対象に含む。[RunWorkCore.lean](../Riftbound/Invariant/RunWorkCore.lean)

### 3ao. 実行中の Play から Chain の終了まで

実行中の `Play` を盤面に照らして検査する。その時点で対象選択と Spell の解決に進まない場合は、生成された Unit や Gear のプレイ計画と、検査済みの後続命令を有限の手順で処理する。Chain 上では検査を直前の合法な Pass につなぎ、処理中に新たな入力を待つか、Chain Item を片付けて次の入力を準備する。通常の優先権を準備する場合、後続に Combat の参加者を更新するフレームがないことを仮定する。Champion Zone の合法な起動が生成した命令列で、最後の Pass から進めた結果と照合する。[RunWork.lean](../Riftbound/Invariant/RunWork.lean) [ChainAnswerWork.lean](../Riftbound/Invariant/ChainAnswerWork.lean)

### 3ap. 効果の途中で Spell を解決する

Spell を解決する実際の命令列を検査し、Spell 本体、Trash への移動、Cleanup、元の効果の残りを有限の手順で処理する。途中で入力が必要ならそこで待つ。この経路を Chain の最後の合法な Pass までつなぎ、カードをプレイしたイベント、ドロー、Spell の解決完了を順に記録することをテストする。[RunWork.lean](../Riftbound/Invariant/RunWork.lean) [ChainAnswerWork.lean](../Riftbound/Invariant/ChainAnswerWork.lean)

追加コストなどの選択を後で行う Spell では、先に元の効果を終え、待機していた Spell を既存の確定処理に渡す。Trash から Spell をプレイする `castInline` 命令も、Spell の確定を予約して元の命令に戻るところまで停止検査で扱う。[RunWorkCore.lean](../Riftbound/Invariant/RunWorkCore.lean) [LimitedSpellWork.lean](../Riftbound/Invariant/LimitedSpellWork.lean)

### 3aq. 効果の解決中にプレイするカードを選ぶ

候補がなければ元の効果の残りを実行し、候補が複数あれば選択を待つ。候補が1枚の場合と、プレイヤーが合法な候補を選んだ場合は、選択イベントの処理後に先頭の Play を検査する。その時点で Play が先頭にあり検査を通る経路では、通常の誘発を保持したまま Play と Chain Item の解決を進められる。選択の直後に即時 Add が先頭に載る経路は、追加の合成が残る。実際の起動、最後の Pass、複数候補への回答を通して、選択とプレイのイベント順、未選択カード、元の効果の再開を確かめる。[RunWork.lean](../Riftbound/Invariant/RunWork.lean) [ChainAnswerWork.lean](../Riftbound/Invariant/ChainAnswerWork.lean) [Chain.lean](../RiftboundTest/Chain.lean)

## 4. 進め方の案（単位に分ける）

| 単位 | 内容 | 大きさの見込み |
|---|---|---|
| I12a | `Cleanup` の停止: 測度 1〜6 と、`killObj` が場の数を減らす補題 | 実際のイベント処理、同時撃破、入れ子の死亡置換を含めて証明済み |
| I12b | `run` の停止 | 制御構文の合成、観測まで含めた即時 Add、直接・相互・振り分けダメージ、支払い時の Recycle、手札やデッキ上部の閲覧・公開を伴う効果は証明済み。残りの効果と、実行時に作られる作業フレームまで含む一般証明が残る |
| I12c | 段階、`triggers`、Chain の解決、Combat と、全体を `advance` にまとめる | 通常の Pass、対応する Chain の最後の Pass、Chain の対応する効果への回答、Showdown の Pass と割り当てから次の決定点までの停止は証明済み。誘発の支払い、カードのプレイと能力起動、および対応する死亡置換の回答も証明済み。通常移動、グループ移動、Showdown の戦場選択、対応する Cleanup への回答も扱う。基本 Rune と即時 Add の合法な起動、Predict、カード名の指定、カード種別の推測も含む。2 対 2 の招待と辞退、および対応する War の投了についても証明済み。残る入力や効果と作業フレームの合成が残る |
| I12d | 全体: 「`WF` な状態からの `advance` は、ある fuel で `fuelExhausted` にならない」 | 小（上がそろえば） |

**fuel で扱う部分の線引き**（roadmap の約束）: 証明が終わるまでは、`fuelExhausted` が**そのまま返る**（隠さない）。証明が終わっても、「ある fuel」は存在を言うだけで、100 で足りるかどうかは、**上の測度から数えた上限**を別に示さない限り、テストで確かめる（`RiftboundTest/Fuel.lean`）。

## 4b. 計画の見直し（I12c は、単独では成り立たない）

I12a のあとで、I12c（残りの作業フレームの停止）を、新しい道具なしで、フレームごとに小さい測度で示せると書いた。**これは誤りだった**。理由:

- 作業フレームは、**積み替えで増える**。`beginTurn` は 6 個のフレームに、`run` は複数の `run` に、置き換わる。測度が「先頭のフレームの階数」だけだと、先頭が下がりながら、積みの長さが増えて、終わらない列（`[1]` → `[0,1]` → `[0,0,1]` → …）が作れてしまう。**積み全体を測る、多重集合の順序（Dershowitz-Manna）か、それと同じ強さの道具が要る**。
- 階数が有限個で上から押さえられるなら、「各階のフレームの数」の組を、高い階から字引き順に比べればよい（I12a の `MeasLt` と同じ形）。**階数の上限は、`run` では、カードの効果の木の深さ**（`CardDB` は変わらないので、有限）。`cleanup` は、積みの階数が同じで、中の測度（I12a）が減る。
- **`withTriggers` が、毎歩、積みの上に `triggers` フレームを足す**（イベントが起きたとき）。置き換えではなく、追加なので、測度が増える。ただし、`triggers` は、能力を Chain に置き、`chainPass`（決定フレーム）で `advance` を止めるので、「足されたら、あと有限歩で止まる」と別に示し、積みの測度と組み合わせる必要がある。

つまり、I12 の残りは、**I12b、I12c、I12d を 1 つの設計として**進める必要がある。大きい単位で、小さく分けて報告できる形（階数の設計、`run` の測度、`triggers` の扱い、まとめ）に、組み直す。

## 5. 何が言えて、何が言えないか（今）

- Cleanup と Expiration が連続する区間、初期手札、対局中のドロー、通常の誘発キューには証明済みの範囲がある。効果の制御構文の有限性と、検出済みの即時 Add が実際のエンジンで元の処理に戻ることを証明した。
- 次の決定点までの停止を示すには、イベント処理による割り込みや、残りの効果・Chain・Combat を含む作業フレームをまとめる必要がある。
