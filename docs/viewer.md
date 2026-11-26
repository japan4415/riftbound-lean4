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

外部の対局から記録を起こす場合は、アーカイブの `input` と同じ形の JSON を作り、`riftbound-replay record INPUT.json ARCHIVE.json` で照合用の記録を作る。`answers` にはシャッフル後のオブジェクト順、選択、支払い、時計やジャッジの決定を、適用された順に入れる。`observed` は直接観測した答え、`inferred` は根拠付きの推定、`unknown` は答えを確定できない箇所。推定を含むマッチは `exact: false` になり、`unknown` では該当する手で止まる。

ゲームごとの `uncheckedCards` は、各席の登録に含まれる `full` 未満のカードを示す。`exact` は操作と2v2の初期手番順の観測状態を示し、カードの実装状況は `cardsFullyChecked` と `uncheckedCards` で確認する。

ジャッジが大会で選択した Constructed Bo1 の準備手順（TR 406.1.h）を記録する場合は、最初のゲームの `bo1Setup` に2席の元の登録を、`decks` にサイドボード後の登録を入れる。`answers` には各席の Battlefield の抽選、先手の決定、`"bo1Sideboard"`、Main Deck と Rune Deck のシャッフルを順に記録する。入れ替えがないときも、`"bo1Sideboard"` は準備手順の区切りになる。ビューアのログで確定前後を確認できる。

Sealed や Draft のサイドボードを照合する場合は、`limitedPools` に各席が受け取ったカードの ID を、同じカードの枚数も含めて登録する。ゲームごとに選んだデッキを `games[].decks.limited.decks` に記録する。Basic Rune はプール外から持ち込める。ブランクの Battlefield は `{"code":"TKN-LimitedBlank"}` で表す。

時間制限付きシングルエリミネーション（TR 408.4）は、ライブ対局の設定 JSON に `"singleElimination": true`、外部の大会記録に `"elimination": {}` を指定する。ゲームの合間に時間切れとなり、勝数が同じため次のゲームを行う場合は、`elimination.timeAfterGames` に時間切れ時点で終了していたゲーム数を入れる。次のゲームは初手番に加えて5ターンを行い、同点ならサドンデスになる。ビューアでは期限のターンと、サドンデスに入った手を確認できる。

### ジャッジの裁定

登録デッキを使う大会では、ライブ画面で「ジャッジの裁定を記録」を開くと、対象席を選んでゲームロス、マッチロス、失格によるマッチ終了を記録できる。ゲームの合間に記録したゲームロスは次のゲームの開始時に適用する。同じ時点で両チームにゲームロスが適用される場合は、対象をまとめて選ぶとゲームが引き分けになる（TR 701.2.b–d）。マッチロスと失格はマッチの勝敗を記録し、大会の順位表は別途扱う。

外部記録では、ゲームロスが適用された位置の `answers` に `{"gameLoss":{"seats":[{"n":1}]}}` を入れる。2v2ではそのゲームの `ending` にも同じ対象席を記録する。公開済みの名前付きBattlefieldは、以後のゲームで同じ席が使うと照合時に拒否される（TR 406.1.c）。マッチロスや失格は、マッチ全体の `ending` に `{"matchLoss":{"seat":{"n":1}}}` または `{"disqualification":{"seat":{"n":1}}}` を記録する。

標準入力では `judge-game-loss SEATS`、`judge-match-loss SEAT`、`judge-disqualification SEAT` を使う。`judge-game-loss 13` は P1 と P3 への同時裁定を表す。

プレイを巻き戻した場合は「ジャッジの裁定を記録」で戻す手を指定する。巻き戻す前の操作もログに残る。外部記録では `{"judgeRewind":{"target":18}}` を裁定位置の `answers` に置く。手番号は初期状態を0とする。現在は、時計や別の裁定を挟まない同じゲームのプレイ区間を戻せる。非公開カードをランダムに選び直す手順は今後の対象。

山札の一部をジャッジが混ぜ直した場合は、変更した位置と混ぜ直した後のオブジェクトIDを保存する。ライブ画面の「裁定シャッフルを読み込む」では `seat`、`deck`（`"mainDeck"` または `"runeDeck"`）、`positions`、`order` を持つJSONを使う。位置は山札の上を0として昇順に並べ、`order` の各IDは `{"n":42}` の形で同じ順に並べる。外部記録では `{"judgeShuffle":{"shuffle":{...}}}` としてそのJSONを入れる。選んだ位置にあったカードの集合を照合し、他の位置とゲーム内のシャッフル誘発には影響させない（TR 701.4）。

標準入力では `judge-rewind CHECKPOINT` と `judge-shuffle SHUFFLE_JSON` を使う。

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
