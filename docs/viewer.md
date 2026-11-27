# トレースビューア

エンジンが進めたゲームをアニメーションで再生する。マッチの記録では、ゲームを切り替えて各手を確認できる。ルールの判定は Lean が行う。

```
RiftboundDriver/Trace.lean ──JSON──▶ viewer/index.html（再生）
  step でゲームを進めて記録              ルールを持たない
```

## 使い方

```sh
lake build riftbound-trace
.lake/build/bin/riftbound-trace 1 4 > trace.json          # seed 1、4 ターン
uv run --no-project python scripts/build_viewer.py trace.json game.html
open game.html
```

`viewer/index.html` を直接開くと、書き出した JSON を選んで読み込める。`build_viewer.py` はトレースを埋め込み、1 ファイルで開ける HTML にする。

画面の操作は、再生と停止、1 手の前後、最初と最後、スクロールバー、速度、ログの行のクリック。キーボードは空白（再生と停止）と左右の矢印。`prefers-reduced-motion` のときは動かさない。

## トレースの形

`{seed, players, cards, steps}`。`cards` はカード ID からの名前・タイプ・ドメイン・コスト・Might。`steps` は 1 つの答えごとに 1 つで、先頭は答える前の状態。

| 項目 | 内容 |
|---|---|
| `action` | 答えた者（`p0`・`chance` など）と、答えの種類 |
| `events` | `step` が返した `Event`（`moved` の旧 ID と新 ID、移動先のゾーンなど） |
| `state` | 答えたあとの状態: ターン、フェーズ、手番、得点、Rune Pool、ゾーンごとの ID の並び、Exhaust と傷の印 |
| `state.new` | その手で初めて現れたオブジェクト（ID は増える一方で、再利用されない） |

カードの移動は、`moved` の旧 ID から新 ID への対応で追う。山札などの山は、枚数だけを表示し、カードを引くと山の位置から手札へ動く。

## 何が保証されて、何がされないか

- 見えている盤面は、`step` が返した状態そのもの。`legalActions` が許した答えだけで進めている（Driver の方針は `demoAnswer`: Rune を Exhaust し、偶数ターンは 1 枚 Recycle して、パスする）。
- **JSON への変換（`Trace.lean`）と画面の描画は、Lean の証明の対象外。** 見え方のおかしさは、エンジンの誤りと、ここの誤りの両方がありうる。
- 今の `Event` は移動・得点・Burn Out だけなので、Rune Pool と Exhaust の変化は、状態の差から描く。
- デモのデッキ（`Demo.lean`）は、テストの fixture と同じ形の仮のカード。実際のカードではない。

## ライブ操作（画面から答えを選んで進める）

人が、画面のボタンで合法手を選んで、ゲームを進める。**ルールは Lean だけにあり、画面も橋渡しも持たない。**

```
viewer/index.html ──HTTP(JSON)──▶ scripts/live.py ──標準入出力(1 行 1 コマンド)──▶ riftbound-live（Lean）
 ボタンを描く、押した番号を送る      127.0.0.1 だけで待ち受ける            legalActions と step、JSON を返す
```

```sh
lake build riftbound-live
uv run --no-project python scripts/live.py            # http://127.0.0.1:8765/ を開く
```

「新しいゲーム」で、seed と、操作する席（P0、P1、両方）を選ぶ。操作しない席と、乱数の質問（シャッフル、Battlefield、手番順）は、`demoAnswer` が自動で答える。ボタンは `legalActions` のうち、操作する席の答えで、投了も含む。押すと、Lean が `step` で進め、操作しない席の自動の答えも含めた手が、アニメーションで再生される。ログの行を選ぶと、前の手を見られる（そのときボタンは隠れる）。

**決めたこと**（Issue #14 の問い）:

| 問い | 決めたこと |
|---|---|
| 通信方式 | Python が localhost の HTTP を Lean の標準入出力につなぐ。1 行で 1 コマンドを送り、`act` には直前の合法手の番号を渡す。登録付きの開始とデッキ変更は、コマンドの引数に JSON を渡す |
| 状態を丸ごと送るか | 手ごとに、トレースと同じ形の状態を丸ごと送る（`state.new` で、初めて現れたオブジェクトだけを足す）。差分は使わない |
| `Event` に Rune Pool と Exhaust の変化を足すか | 足さない。今までどおり、状態の差から描く |
| 操作する席 | 画面で選ぶ（P0 だけ・P1 だけ・両方）。もう一方は `demoAnswer` |

**橋渡しの安全**: `127.0.0.1` だけで待ち受け、Host と Origin を確かめ、POST は `application/json` だけを受ける。ゲームは 1 つ。ブラウザからは Artifact のページのように外へ通信できない場所では動かない（ライブ操作の欄は、橋渡しが見つかったときだけ出る）。

**ルールと試合の選択**:

- ルール: Core Rules（デモ）、大会の Constructed、大会の Sealed、大会の Draft（Sealed と Draft は、Legend も Chosen Champion も無いデッキで、最初のターンの追加ドローがある）。
- 大会のルールでは、画面に「**時計: 時間切れを知らせる**」（今のターンと、さらに 3 ターンで終わる: TR 408.2）と「**ジャッジ: 引き分けを宣言する**」（TR 410.1、505.6）のボタンが、合法なときだけ出る。合法かどうかは Lean が決める。
- 試合: 「1 ゲームだけ」「Best of 1」「Best of 3」。ゲームが終わると、結果がマッチ（`MatchState`）に数えられ、画面に勝ち数・サイドボードが使えるか・次の先手の決め方が出る。続くとき、「次のゲーム」のボタンが出る。**先手か後手かを選ぶのが、操作する席のプレイヤーなら、画面で選ぶ**（最初のゲームは、seed で抽選された人。その後は、負けた人。引き分けの後は、同じ順: TR 407）。選ぶのが自動の席なら、先手を選ぶ。

大会の Constructed でサイドボードを使えるときは、画面に Main Deck とサイドボードのカードが枚数つきで出る。出すカードと入れるカードを1枚ずつ選んで「入れ替える」を押すと、Lean が変更後のデッキの合法性を確認する（TR 403.4.c）。通常は勝敗がついたゲームの後に使える。下記の任意のBo1手順では、初戦の準備中に使える。

画面には双方の手札が表示される。両席を人が操作する場合は、この表示を含めて同じ画面を使う。

## 実カードの登録とマッチの保存

`lake build riftbound-live riftbound-replay` を実行し、上の手順でライブビューアを開く。「登録デッキで開始」から [Constructed の設定例](../data/replay/constructed-example.json) を読み込むと、実カードを使って Bo3 を始められる。操作する席を「両方」にすれば、双方の手を選べる。設定ファイルの型は `LiveSetup`。

- `decks` に両席のデッキを席番号順に入れる。カード ID は `data/cards/logical.json` の `cardId` を使う。Constructed は登録時のサイドボードを含める。
- `config` にゲーム形式とカードの合法性を入れる。公式 Constructed の `tournament` を指定すると、開催日・禁止改定の適用区分と `formatLegality` の整合性を確認する。`firstChooser` は最初の先手・後手を決める席。通常の手順では `first` の席が先手になる。
- サイドボードの変更が許されているときは、その席の変更後の `ConstructedDeck` を JSON で読み込める。`decks.constructed.decks` の各要素と同じ形で、複数枚と Chosen Champion をまとめて変更できる。引き分けの後は先手と Battlefield を引き継ぐ。
- 大会が任意の初戦サイドボード手順を使う場合は、Constructed の設定に `"winsRequired": 1` と `"bo1Sideboarding": true` を指定する（TR 406.1.h）。Battlefield の抽選後、`firstChooser` の席を操作していれば、画面で先手か後手かを選ぶ。自動の席が選ぶ場合は設定の `first` が先手になる。編集を終えたら「サイドボードを確定」を押す。Chosen Champion を配置してからシャッフルが始まり、アーカイブには変更前後の登録と確定した手が残る。
- ゲームの合間に時間切れになったら「時間切れ」を押す。その時点の勝ち数でマッチが決まる。マッチ全体の投了と合意した引き分けは、標準入力プロトコルの `concede-match SEAT` と `agree-match-draw` で記録できる。
- マッチ終了後に「マッチの記録を保存」を押す。アーカイブには両席の手札を再現できるデッキ順が含まれる。個々のゲームはビューアの「ゲーム」欄で切り替えられる。

### 別のプロセスで照合する

```sh
.lake/build/bin/riftbound-replay verify riftbound-match.json
.lake/build/bin/riftbound-replay view riftbound-match.json match-trace.json
uv run --no-project python scripts/build_viewer.py match-trace.json match.html
```

`verify` はアーカイブのルール版とカード定義を照合し、すべての手を再実行する。各手で状態のハッシュとイベント列を比較し、違いがあれば最初のゲーム番号と手の位置を出す。`view` で書き出した JSON はビューアの「対局記録を開く」からも読み込める。

カード定義の識別子は、使われなかったカードの効果や実装状況を更新しても変わる。後から検証する記録には、記録時に使った実行ファイルか、その実行ファイルを再ビルドできる Git コミット ID を一緒に保存する。

外部の対局から記録を起こす場合は、アーカイブの `input` と同じ形の JSON を作り、`riftbound-replay record INPUT.json ARCHIVE.json` で照合用の記録を作る。`answers` にはシャッフル後のオブジェクト順、選択、支払い、時計やジャッジの決定を、適用された順に入れる。`observed` は直接観測した答え、`inferred` は根拠付きの推定、`unknown` は答えを確定できない箇所。推定を含むマッチは `exact: false` になり、`unknown` では該当する手で止まる。

カードの並びを直接確認できた場合は、内部IDの代わりに
`{"observedChance":{"outcome":{"cardOrder":{"cards":[{"code":"OGN-001"},{"code":"OGN-002"}]}}}}`
の形で記録できる。シャッフル前にあったカードを、同じカードの枚数も含め、結果の順番で全て並べる。山札は上から順に指定する。
この形式は山札のシャッフル、マリガン、Burn Out、Predict、Trash からのランダムなリサイクルに使える。
Battlefield の抽選は `{"observedChance":{"outcome":{"battlefield":{"card":{"code":"RAD-157"}}}}}` の形で、選ばれたコードを指定する。
後から推定した結果には `inferredChance` を使い、`outcome` と根拠を記した `evidence` を入れる。

同じコードの現物を区別できない場合、シャッフル前の並びから未使用の現物を順に割り当て、`exact: false` を記録する。
現物まで特定できる場合は `observed` でIDを指定できる。
`exact` は操作と2v2・War の初期手番順をどこまで特定できたかを示す。カードの実装状況は `cardsFullyChecked` と `uncheckedCards` で確認する。`uncheckedCards` はゲームごとに、各席が登録した `full` 未満のカードを示す。

マリガン、捨て札、Predict、戦闘ダメージの割り当ては `{"observedCardPick":{"choice":{"seat":{"n":0},"kind":"mulligan","card":{"code":"OGN-001"}}}}` のように、選択した席とカードのコードで記録できる。`kind` は `mulligan`、`discard`、`predictTop`、`predictRecycle`、`assignDamage` のいずれか。該当する合法手が1つならその手を適用する。同じコードのカードを複数選べる場合は列挙順の最初を採用し、`exact: false` になる。後から推定した選択は `inferredCardPick` の `choice` と `evidence` に記録する。これらの手は `inspect` の候補欄にも `answerByCode` として出る。

ジャッジが大会で選択した Constructed Bo1 の準備手順（TR 406.1.h）を記録する場合は、最初のゲームの `bo1Setup` に2席の元の登録を、`decks` にサイドボード後の登録を入れる。`answers` には各席の Battlefield の抽選、先手の決定、`"bo1Sideboard"`、Main Deck と Rune Deck のシャッフルを順に記録する。入れ替えがないときも、`"bo1Sideboard"` は準備手順の区切りになる。ビューアのログで確定前後を確認できる。

Sealed や Draft のサイドボードを照合する場合は、`limitedPools` に各席が受け取ったカードの ID を、同じカードの枚数も含めて登録する。ゲームごとに選んだデッキを `games[].decks.limited.decks` に記録する。Basic Rune はプール外から持ち込める。ブランクの Battlefield は `{"code":"TKN-LimitedBlank"}` で表す。

時間制限付きシングルエリミネーション（TR 408.4）は、ライブ対局の設定 JSON に `"singleElimination": true`、外部の大会記録に `"elimination": {}` を指定する。ゲームの合間に時間切れとなり、勝数が同じため次のゲームを行う場合は、`elimination.timeAfterGames` に時間切れ時点で終了していたゲーム数を入れる。次のゲームは初手番に加えて5ターンを行い、同点ならサドンデスになる。ビューアでは期限のターンと、サドンデスに入った手を確認できる。

#### 外部対戦を入力している途中で次の手を確認する

```sh
.lake/build/bin/riftbound-replay inspect INPUT.json 2 next.json
```

第2ゲームを調べる例。ゲーム番号は1から始まる。2v2 は `inspect-team`、FFA は `inspect-ffa` を使う。FFA のゲーム番号は1。
指定したゲームより前はゲームの終了まで照合する。指定したゲームでは `answers` が尽きるか、最初の `unknown` に達するまで再生する。調査中はマッチ全体の `ending` を省略できる。2v2 では調べるゲームの `battlefields`、`points`、`ending`、`timed` も省略できる。

- `checkpoint` は適用済みの手番号。初期状態は0。`nextAnswer` は次に入力する手番号で、ゲーム終了時は `null`。`missing` は `unknown` に記録した説明、`exactPrefix` は再生済みの手と初期順序が確定しているかを表す。
- `state` に盤面とオブジェクトID、`choices` に現在の決定点で入力できる操作が出る。元の対戦で行われた操作を確認し、対応する `answer` を `answers` に入れる。`decision` が `cardOrder` のときは、カードの集合から観測した並びを作る。
- この出力は転記者向けで、全席の手札や山札を含む。試合全体を照合するときは、結果と未記入の操作をそろえてから `record`、`record-team` または `record-ffa` を実行する。

#### 映像や対戦ログで確認した情報を照合する

ゲームの入力に `observations` を指定する。1対1 と 2v2 は `games[]`、FFA は `game` に置く。`checkpoint` は適用した操作の数で、初期状態は0。映像の時刻やログの行番号は省略可能な `source` に記録できる。

```json
{
  "observations": [
    {
      "checkpoint": 18,
      "source": "映像 00:03:21",
      "facts": [
        {"turn": {"number": 4}},
        {"score": {"seat": {"n": 0}, "points": 2}},
        {"zoneCount": {"zone": {"player": {"p": {"n": 1}, "k": "hand"}}, "count": 3}}
      ]
    }
  ]
}
```

- 得点（`score`）、ターン（`turn`）、フェイズ（`phase`）、手番（`active`）、時間切れの宣言（`clockCalled`）、ゲームの結果（`result`）を照合できる。席番号は0から始まる。2v2 の `score` には、その席のチームの得点を入れる。
- `xp` は各席の未使用 XP を照合する。たとえば `{"xp":{"seat":{"n":0},"amount":3}}` で席0の XP が3であることを確認できる。
- `poolResource` は指定した席の Pool に残っている Energy や Power を種類ごとに照合する。`{"poolResource":{"seat":{"n":0},"resource":"spellEnergy","amount":2}}` は席0の Spell 専用 Energy が2であることを表す。`resource` には `"energy"`、`"unitEnergy"`、`"spellEnergy"`、`"anyPower"`、または `{"domainPower":{"domain":"mind"}}` のようにドメインを指定した Power を使う。観測できた種類だけを記録できる。
- 公開ゾーンにあるカードを全て確認できたときは `zoneCards`、映像に一部だけ映ったときは `zoneContains` を使う。どちらも `zone` と `cards`（`[{"code":"RAD-094"}]` など）を指定する。並び順を問わず、同じコードの枚数を数える。手札・山札・伏せ札は `zoneCount` で枚数を照合できる。
- `battlefieldControl` は Battlefield の支配者、`battlefieldUnits` はその Battlefield にいる指定プレイヤーの Unit を照合する。どちらも Battlefield を持ち込んだ席を `owner`、現在のカードコードを `field`、確認する席を `controller` に入れる。`battlefieldUnits` では `cards` に全 Unit のコードを入れる。`battlefieldControl` の `controller: null` は支配者なしを表す。

- `unitStates` は Unit のカードコード、Exhaust の有無、与えられたダメージを照合する。`controller` に席、`place` に `"base"` または `{"battlefield":{"owner":{"n":1},"field":{"code":"RAD-157"}}}` を指定する。`units` にはその席がその場所でコントロールする全 Unit を `{"card":{"code":"RAD-026"},"exhausted":true,"damage":2}` の形で入れる。同名の Unit はそれぞれ記録し、並び順は問わない。
- `markedUnits` は同じ `controller` と `place` の指定で、`marker` が `"buffed"` または `"stunned"` に当てはまる全 Unit のコードを `cards` に入れる。同じコードの Unit が複数該当する場合は枚数分を記録する。
- `unitAttachments` は、同じ `controller` と `place` の指定で Unit ごとの装備を照合する。`units` に `{"unit":{"code":"OGN-051"},"attached":[{"code":"SFD-009"}]}` の形で全 Unit を入れる。装備が無い Unit は `"attached":[]` にする。同じコードの Unit が複数いても、どの装備が同じ Unit に付いているかを照合できる。

- `visibleZoneContains` は、席別の画面や本人の記録で確認した手札などのカードを照合する。見た席を `viewer`、そのカードがあったゾーンを `zone`、確認できたカードを `cards` に入れる。たとえば Predict でその席に開示された山札のカードを指定できる。
- `chainOrder` の `items` には、Chain の一番上から順に全項目を入れる。Spell は `{"spell":{"controller":{"n":0},"card":{"code":"SFD-087"}}}`、能力は `{"ability":{"controller":{"n":1},"source":{"code":"SFD-046"}}}` とする。能力の発生元が盤面を離れた後も照合できる。
- `hiddenAt` は、`seat` の伏せ札のうち、`owner` が持ち込んだコード `field` の Battlefield にある枚数 `count` を照合する。公開された伏せ札の位置と枚数から記録できる。
- `eventsInOrder` は、そのチェックポイントに進んだ一手の中で起きた公開イベントを順番に照合する。`events` に `[ {"discarded":{"seat":{"n":0}}}, {"drew":{"seat":{"n":0}}} ]` を入れると、席0が捨ててから引いたことを照合できる。映像に映らなかったイベントは省略でき、同じイベントを複数入れるとその回数も照合する。使える名前は `drew`、`discarded`、`recycled`、`playedCard`、`playedToken`、`buffedUnit`、`burnedOut`、`pointsGained`。`pointsGained` には `seat` と `points` を入れる。チェックポイント0のイベント列は空。

`record` と `verify` は、指定した観測を全て照合する。不一致は最初に食い違ったゲーム、手番号、項目、期待値と再生結果を示す。`inspect` は再生できた手までを照合し、そのゲームの照合済み件数と後の手に残った件数を `checkedObservations` と `pendingObservations` に出す。

#### カード定義を更新した後に再照合する

```sh
.lake/build/bin/riftbound-replay revalidate riftbound-match.json checked-match.json
.lake/build/bin/riftbound-replay verify checked-match.json
```

カード定義を更新したら、`revalidate` で以前のアーカイブを現在の実行ファイルで照合できる。2v2は `revalidate-team`、FFAは `revalidate-ffa` を使う。保存形式とルールの版が同じ場合に、初期状態と各手の状態ハッシュ、イベント列、勝敗を照合する。一致すれば、現在のカード定義の識別子と実装状況を反映したアーカイブを書き出す。出力には別のファイル名を指定し、元の記録を保管する。

新しいアーカイブでは、各チェックポイントの `chosenChampions` に、席番号と登録した Chosen Champion の物理 ID の組を記録する。Bo1 では初回のサイドボード確定時に登録される。古いアーカイブはこの項目がなくても状態ハッシュとイベント列で照合でき、`revalidate` の出力に登録情報が加わる。

同じく `playEnergy` には、そのターンのプレイ履歴順にエナジー支払いを記録する。呪文をプレイする費用を確定した記録に支払い額を、ほかの記録に0を入れる。この項目を含むアーカイブは支払い額まで照合し、古いアーカイブを再照合した出力にも追加する。

`playPhysical` は同じ履歴順の物理カードIDを照合する。手札に戻るなどして盤面上のオブジェクトIDが変わっても、同じカードを追跡できる。

`playStamps` は同じ履歴順に、プレイを確定した時点の内部タイムスタンプを照合する。「次にプレイするカード」に効く効果がどのプレイまで有効だったかを確認できる。

`buffAttributions` は、Buff を実行した席と、その入力で発行されたイベント列における0始まりの位置を照合する。旧アーカイブも元の Buff イベントを使って再照合できる。

再生内容が変わった場合は、最初に差が出たゲーム番号と手番号が分かる。保存形式やルールの版が異なる場合は、記録時に使った実行ファイルで照合する。

#### 公開・閲覧の履歴を席別に書き出す

```sh
.lake/build/bin/riftbound-replay disclosures riftbound-match.json 0 disclosures-p0.json
```

`disclosures` は、指定された席が公開または閲覧で見たカードを、ゲームと手の順に JSON に書き出す。席番号は0から始まる。2v2 は `disclosures-team`、FFA は `disclosures-ffa` を使う。同じ手の途中でカードが移動し、決定点に元のオブジェクトが残らない場合も、見えた時点のカードを記録する。

この出力に含まれるのは公開・閲覧の履歴。ジャッジが巻き戻した場合も、各席がその時点で見られたと再現された内容は元の手に残る。推定した手を含む記録では `exact` が `false` になる。アーカイブと通常の `view` の出力には全席の情報が含まれるため、席ごとに履歴を渡すときは `disclosures` の出力を使う。

#### 各手の盤面を席別に書き出す

```sh
.lake/build/bin/riftbound-replay view-seat riftbound-match.json 0 board-p0.json
```

2v2 では `view-team-seat`、FFA では `view-ffa-seat` を使う。記録を検証し、各ゲームの初期状態（`i: 0`）と各手の決定後の状態を `games[].steps` に出力する。各手では盤面、ターン、得点、勝敗、指定席に見えた公開・閲覧の履歴を確認できる。`judgeRewind` は戻し先の手番号を表す。推定した手を含む記録では `exact` が `false` になる。

`state.zones` のうち、山札と他席の手札の裏面は `null` で表す。公開・閲覧の効果が続いている間は、その席に見える表面も出力する。自分の手札はカードコード順に並ぶ。伏せ札は支配者と置かれた Battlefield が見え、表面は閲覧権限がある席にだけ出力される。装備先などの参照は `zone` とゼロ始まりの `index` で、その手の盤面内の位置を指す。

Scuttle Crab のように、伏せ札をターン中に閲覧できる権限も席別の盤面に反映される。その間の表面は `visibleZoneContains` で照合できる。履歴に記録される公開・閲覧イベントは、カードが公開されたり、効果の指示で実際に閲覧したりしたときに発生する。

### ジャッジの裁定

登録デッキを使う大会では、ライブ画面で「ジャッジの裁定を記録」を開くと、対象席を選んでゲームロス、マッチロス、失格によるマッチ終了を記録できる。ゲームの合間に記録したゲームロスは次のゲームの開始時に適用する。同じ時点で両チームにゲームロスが適用される場合は、対象をまとめて選ぶとゲームが引き分けになる（TR 701.2.b–d）。マッチロスと失格はマッチの勝敗を記録し、大会の順位表は別途扱う。

外部記録では、ゲームロスが適用された位置の `answers` に `{"gameLoss":{"seats":[{"n":1}]}}` を入れる。2v2ではそのゲームの `ending` にも同じ対象席を記録する。公開済みの名前付きBattlefieldは、以後のゲームで同じ席が使うと照合時に拒否される（TR 406.1.c）。マッチロスや失格は、マッチ全体の `ending` に `{"matchLoss":{"seat":{"n":1}}}` または `{"disqualification":{"seat":{"n":1}}}` を記録する。

標準入力では `judge-game-loss SEATS`、`judge-match-loss SEAT`、`judge-disqualification SEAT` を使う。`judge-game-loss 13` は P1 と P3 への同時裁定を表す。

プレイを巻き戻した場合は「ジャッジの裁定を記録」で戻す手を指定する。巻き戻す前の操作もログに残る。外部記録では `{"judgeRewind":{"target":18}}` を裁定位置の `answers` に置く。手番号は初期状態を0とする。通常の指定では、時計や別の裁定を挟まない同じゲームのプレイ区間を戻せる。

非公開のドローを戻す際にジャッジがカードを選び直した場合は、「巻き戻し裁定の JSON を読み込む」で `target` と `returns` を持つJSONを使う。各要素の `drawn` はドローによって手札に作られたオブジェクトのID。候補の `candidates` と実際に戻した `returned` は、巻き戻し先のチェックポイントにおける各カードのオブジェクトIDで指定する。対象は、巻き戻し先の Main Deck にあったカードのドロー。Burn Out などで途中のオブジェクトIDが変わった場合も、同じ現物を巻き戻し先の山札の位置に対応付ける。複数のドローは後のものから戻し、その時点で手札に残っているカードを候補にする。同じカードを引き直した場合も、ドローごとに別の `drawn` を記録する。後の裁定で別のカードを戻すと、前のドローを戻すときの手札にもその入れ替えを反映する。必要なら `shuffles` に部分シャッフルを含め、プレイを再開する前にまとめて適用できる。その `order` も巻き戻し先のIDを使う（TR 701.5.d.3–4）。外部記録では `{"judgePrivateRewind":{"rewind":{...}}}` としてこのJSONを入れる。

効果で公開してから引いたカードは、巻き戻し先の Main Deck の元の位置に戻る。このドローは `returns` に指定せず、同じ巻き戻しで非公開のドローを戻す際の候補にも含めない（TR 701.5.d.3）。

巻き戻し先の時点から新たに表面が見えた Main Deck や Rune Deck のカードは、その後に引いたり Channel したりしていなければ、巻き戻しの `shuffles` に含める。先に別の裁定で取り消した手で見たカードも、当時の順番を復元する場合は照合する。ドローの戻しが無ければ `returns: []` とする。ジャッジがランダムな部分のないデッキを混ぜずに戻す裁定を下した場合は、`unshuffledDecks` に `{"seat":{"n":0},"deck":"mainDeck"}` のように対象を記録する。この項目は時計や別の裁定を挟む巻き戻しでも使える（TR 701.4.b.1、701.5.d.4）。

時計が鳴る前に戻す場合は `target` と、裁定で確定した最終予定ターン `deadline` を記録する。時計の方式と時間切れが宣言済みであることは引き継ぐ。前の巻き戻しや裁定シャッフルも取り消す場合は、対象の裁定の手番号を `rulings` に新しい順で並べる。以前の巻き戻しで取り消された手は、元のログから参照できる。復元先は現在の進行経路から選ぶ。外部記録では `{"judgeTimelineRewind":{"rewind":{"target":9,"deadline":5,"rulings":[16,12]}}}` の形を使い、必要に応じて `returns` と `shuffles` を追加できる。

山札の一部をジャッジが混ぜ直した場合は、変更した位置と混ぜ直した後のオブジェクトIDを保存する。ライブ画面の「裁定シャッフルを読み込む」では `seat`、`deck`（`"mainDeck"` または `"runeDeck"`）、`positions`、`order` を持つJSONを使う。位置は山札の上を0として昇順に並べ、`order` の各IDは `{"n":42}` の形で同じ順に並べる。外部記録では `{"judgeShuffle":{"shuffle":{...}}}` としてそのJSONを入れる。選んだ位置にあったカードの集合を照合し、他の位置とゲーム内のシャッフル誘発には影響させない（TR 701.4）。

標準入力では `judge-rewind CHECKPOINT`、`judge-private-rewind REWIND_JSON`、`judge-timeline-rewind REWIND_JSON`、`judge-shuffle SHUFFLE_JSON` を使う。

### 2v2 の大会記録

ライブで記録する場合は、操作する席を「4席すべて（2v2）」にして、「登録デッキで開始」から [2v2 Constructed の設定例](../data/replay/team-constructed-example.json) を読み込む。設定の型は `LiveTeamSetup`。最初に手番順を選んだチームを `firstChooser` に、選ばれた手番順を `order` に入れる。ゲームに勝敗がつくと負けたチームが次の手番順を選び、引き分けなら直前の手番順と Battlefield を引き継ぐ。

Sealed では `tournament` に代えて `sealed` に両チームの共有プールを入れ、`decks.limited.decks` に最初の4席の登録を入れる。2ゲーム目以降はサイドボードを使えるときに4席の `LimitedDeck` をまとめて読み込める。次のゲームを始めるときに、共有プールの枚数と Battlefield の使用履歴を照合する。

対局終了後に「マッチの記録を保存」を押し、`riftbound-replay verify-team riftbound-match.json` で照合する。標準入力から操作する場合は `start-team-json SEED HUMANS SETUP`、`team-next [ORDER|- [SEALED_DECKS]]`、`replay` を使う。たとえば `team-next 1302` は P1、P3、P0、P2 の順に次のゲームを始める。

`riftbound-replay check-team TEAM.json` は、`TeamMatchRecord` の4席分の登録、チーム A/B の手番順、選ばれた Battlefield、共有得点から決まるゲームとマッチの勝敗を確認する。

操作列を記録できた試合では、`riftbound-replay record-team TEAM.json ARCHIVE.json` と `riftbound-replay verify-team ARCHIVE.json` で、ゲームごとの入力と状態を再照合できる。操作列に使う席番号は第1チームの A/B が 0/1、第2チームの A/B が 2/3。`order` を使って開始時の手番順を設定するため、最初の入力は最初のシャッフル。Battlefield の選択は先手以外の3席分を記録する。

先手は交互に並んだ A/B の順序上のどの席からでも選べる（TR 603.7.c）。たとえば、第1チームの B が先手で第2チームの B が次なら `order` は 1、3、0、2。引き分け後は同じ4席の順序を使う。

初期手番順を推定した場合は、`order` に推定した順を、`openingOrderEvidence` に `{"inferred":{"evidence":"映像は2人目の手番から始まり、以後の手番から推定"}}` のように根拠を記録する。この場合は `exact: false` になる。順序を確定できない場合は、`order: []` と `{"unknown":{"description":"初期手番が映っていない"}}` を記録する。照合は該当ゲームの開始前で止まる。直接観測した場合は `openingOrderEvidence` を省略する。

2v2 Sealed の場合は `sealed.team0` と `sealed.team1` に、各チームが開封した8パックの中身を記録する（TR 603.6）。各ゲームの `sealedDecks` に4席の Limited デッキを入れる。プールにあるカードの枚数をチーム内で合算し、サイドボードの利用可否と Battlefield の使用履歴を確認する。Bo1 では各席に3枚の候補を登録する。Bo3 では Battlefield を出す席が選んだ1枚だけを登録し、操作列にはその候補を確定する `pick 0` を入れる。Bo3 の先手席は候補を空にできる。

ゲーム途中にマッチ投了や合意の引き分けで終了した場合、最後のゲームの `ending` を `"matchEnded"` にする。そこまでの操作と終了時点の得点を照合し、そのゲームはマッチのゲーム勝数に加えない。

2v2 のシングルエリミネーションも `elimination` で指定する。サドンデスで決まったゲームは `ending` に `{"suddenDeath":{"team":{"n":0}}}` の形で得点したチームを記録する。

`record-team` と `verify-team` の出力には `exact` と `cardsFullyChecked` が含まれる。`exact` は操作と初期手番順をすべて直接観測した場合に `true` になる。カードの実装状況は `cardsFullyChecked` と席別の `uncheckedCards` で確認する。

`riftbound-replay view-team ARCHIVE.json TRACE.json` で検証済みの対局を閲覧用に変換できる。既存ビューアの「閲覧用 JSON」から `TRACE.json` を開くと、チームの所属、ゲーム勝数、招待や Battlefield の選択を追える。

4席のセットアップ、手番、チームの共有得点、スイスラウンドの時間切れや投了まで再実行できる。味方が得点ステップで占めていた Battlefield は、そのターンの Final Point 判定にも使う。味方がいる Battlefield への移動を制限し、Combat の参加者やカード効果の対象を判定するときはチームを区別する。

Main Phase の Neutral Open で味方を招待するときは、手番プレイヤーの `inviteTeammate` と味方の席番号 `guest` を記録する。招待された席は、自分のルーンから支払いを用意してスペルや起動型能力を使うか、`pass` で辞退する。開始できる Showdown や Combat が複数ある場合は、手番プレイヤーが `choose` で Battlefield のオブジェクト ID を指定する。

複数のユニットを同じ場所へ Standard Move で動かすときは、`startGroupMove` に移動先と支払いを指定し、各ユニットの ID を `choose` で記録する。最後の `decide true` で全員が同時に移動し、移動先の追加コストがあれば1回分を支払う。`decide false` で取り消せる。

### 3人戦・4人戦の記録

Skirmish（FFA3）と War（FFA4）は Core Rules の1ゲームを `FreeForAllInputs` で記録する。`mode` には `players`（3 または 4）、`victoryScore`（8）、`battlefieldsInPlay`（3）、`deckBattlefields`（3）を指定する。`game.decks.core.decks` に席番号順のデッキを、`game.answers` にシャッフルや選択を含む操作列を入れる。入力の途中で終わっているゲームは記録エラーになる。

- Skirmish は各席の Main Deck と Rune Deck のシャッフル、3席の Battlefield 選択、`arrangePlayers` による手番順の記録、マリガンの順に進む。
- War は `game.openingOrder` に全4席の手番順を入れる。操作列はシャッフルから始まり、手番順の先頭を除く3席が手番順に Battlefield を選ぶ。手番順を推定した場合は `game.openingOrderEvidence` に、`{"inferred":{"evidence":"映像から推定した根拠"}}` の形で根拠を記録する。
- 席1が投了した場合は、その時点の `game.answers` に `{"observed":{"action":{"actor":{"player":{"p":{"n":1}}},"kind":"concede"}}}` を入れる。2席以上が残る間は、その後の操作も記録する。Skirmish で初期手番順を決める前に投了があった場合、`arrangePlayers` には残った席の順序を指定できる。

```sh
.lake/build/bin/riftbound-replay record-ffa INPUT.json ARCHIVE.json
.lake/build/bin/riftbound-replay verify-ffa ARCHIVE.json
.lake/build/bin/riftbound-replay view-ffa ARCHIVE.json TRACE.json
```

`verify-ffa` では勝者、各席の得点、チェックポイントの一致、観測の確かさ、使用カードの確認状況を調べられる。`TRACE.json` はビューアの「閲覧用 JSON」から開ける。上のコマンドは、Showdown 中に投了がある [4人戦の入力例](../data/replay/war-concession-example.json) で試せる。

## カードの詳細と画像

- カードを右クリックすると、詳細（コスト・Might・キーワード・場所・状態・Lean の定義）が出る。
- **画像**: `viewer/art.json`（カード ID → 画像の URL）があれば、橋渡しが `/art.json` で配り、ページが読んで
  カードに表示する。URL は http(s) だけ。画像は `referrerpolicy="no-referrer"` で読み、読めなければ文字の
  カードに戻る。無いカードは文字のまま。
- 今の `art.json` に入っているのは、デモに出てくる**実在のカード**だけ（Fury Rune = `R1`、
  Sprite = `TKN-Sprite`、Gold = `SFD-T03`）。ほかのデモのカードは、実在しない名前なので、画像は無い。
  URL は公式カードギャラリー（2026-11-22 に一度読んだ）の `cardImage` のもの。
- 公式サイトの URL を集めて保存する仕組みは、別のリポジトリで管理する。
  画像そのものは、このリポジトリに入れない。

## カードをクリックして答える

- 合法手のうち、カードに結びつくものは、**そのカードをクリックして選ぶ**。結びつくのは、Rune の使用（`runeAbility`）、
  カードのプレイ（`playCard`）、マリガン・捨てるカードの選択、Unit の移動（`standardMove`）、
  Combat のダメージの割り当て（`assignPick`）、能力の起動（`activate`、`manaAbility`）。
  盤面にそのカードがあるときだけ結びつけ、無ければボタンのまま。
- 選べる手があるカードは、青い枠で出る（Tab で選んで、Enter でも押せる）。手が 1 つなら、クリックですぐ答える。
  複数あれば（Rune の Exhaust と Recycle など）、メニューが開き、1 つ選ぶ。Escape かほかの場所のクリックで閉じる。
- カードに結びつく手は、下のボタンから隠す。「カードの手も、ボタンで全部出す」で、元のボタンも出せる。
  パス・投了・時計・ジャッジなど、カードに結びつかない手は、いつもボタン。
- どの手が合法かは Lean の `legalActions` が決める。画面は、返ってきた手を、カードに分けて見せるだけ。
- **対象と移動先は、盤面をクリックして選ぶ**。カードの手が「対象」（`playCard`・`activate` の `targets`）か「移動先」
  （`standardMove` の Base か Battlefield）だけ違うときは、カードをクリックしたあと、選べる所が点線で光る
  （対象のカード、Battlefield、自分の Base）。光っている所をクリックすると、その手を選ぶ。対象が複数あるときは、
  1 つずつ順に選ぶ。選べる先が 1 つだけなら、その段は飛ばす。残った違いが、払い方など盤面で選べないものなら、メニューで選ぶ。
  Escape かほかの場所のクリックで、やめる。
- カードの右クリックは、これまでどおり詳細。

**本物の局面での確認**（2026-11-22）: 乱数の種と答えの番号を決めて、ブリッジで同じ局面を作り直せる。
`start SEED 0` のあと、`act` の番号を順に送る。
- 対象の選択: seed 1、番号 `0,1,0,4,0,0,1,5`（8 手）。手札の Counterstrike に、対象が Summoner と Guardian の 2 つの手が出る。
  Guardian をクリックすると、ログに「Counterstrike を Reaction でプレイ（対象: Guardian）」と出る。
- 移動先の選択: seed 3、番号 `2,0,0,2,4,1,1,0,0,0,0,0,1,3,1,0,0,0,0,0,0,0,0,3,7,3,2,0,0,0,0,0,0,0,0,0`（36 手）。
  Base の Looter に、移動先が 2 つの Battlefield の手が出る。Battlefield 2 をクリックすると、
  ログに「Looter を Standard Move」と出て、Looter は Battlefield 2 に移る。

## 1 手戻す

- ライブ操作では、直前の答えを取り消せる（「1 手戻す」のボタン、または Ctrl+Z / Cmd+Z）。何度でも、今のゲームの最初の答えまで戻れる。
- 戻すのは、`riftbound-live`（Lean）が、答える前のゲームを覚えていて、それに戻す。画面は、その手までの記録に切り詰めて、合法手を入れ替える。
- 新しいゲーム、次のゲーム（マッチ）、サイドボードの入れ替えをまたいでは、戻れない。

## 次の段階

時計・ジャッジ・Limited の設定をライブ操作で選べるようにする。カードや Battlefield を直接クリックして答える。
