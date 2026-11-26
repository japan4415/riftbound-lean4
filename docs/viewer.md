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

**サイドボード**: 大会の Constructed のマッチで、サイドボードを使えるとき（最初のゲームの前と、引き分けの後は使えない）、ゲームが終わると、画面に Main Deck とサイドボードのカードが枚数つきで出る。出すカードと入れるカードを 1 枚ずつ選んで「入れ替える」を押すと、Lean が、入れ替えの後のデッキが Constructed で合法かどうかを確かめ（TR 403.4.c）、合法なら受ける。次のゲームは、そのデッキで始まる。

画面には双方の手札が表示される。両席を人が操作する場合は、この表示を含めて同じ画面を使う。

## 実カードの登録とマッチの保存

`lake build riftbound-live riftbound-replay` を実行し、上の手順でライブビューアを開く。「登録デッキで開始」から [Constructed の設定例](../data/replay/constructed-example.json) を読み込むと、実カードを使って Bo3 を始められる。操作する席を「両方」にすれば、双方の手を選べる。設定ファイルの型は `LiveSetup`。

- `decks` に両席のデッキを席番号順に入れる。カード ID は `data/cards/logical.json` の `cardId` を使う。Constructed は登録時のサイドボードを含める。
- `config` にゲーム形式とカードの合法性を入れる。公式 Constructed の `tournament` を指定すると、開催日・禁止改定の適用区分と `formatLegality` の整合性を確認する。`firstChooser` は最初の先手・後手を決める席、`first` は実際に先手で始める席。
- サイドボードの変更が許されているときは、その席の変更後の `ConstructedDeck` を JSON で読み込める。`decks.constructed.decks` の各要素と同じ形で、複数枚と Chosen Champion をまとめて変更できる。引き分けの後は先手と Battlefield を引き継ぐ。
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

ゲームごとの `uncheckedCards` は、各席の登録に含まれる `full` 未満のカードを示す。`exact` は操作の観測状態を示し、カードの実装状況は `cardsFullyChecked` と `uncheckedCards` で確認する。

### 2v2 の大会記録

`riftbound-replay check-team TEAM.json` は、`TeamMatchRecord` の4席分の登録、チーム A/B の手番順、選ばれた Battlefield、共有得点から決まるゲームとマッチの勝敗を確認する。チームの操作列は記録欄に保持できる。個々の操作の再実行は 1v1 のエンジンが対象で、2v2 の対戦処理は [ロードマップの M9](roadmap.md) にある。

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
