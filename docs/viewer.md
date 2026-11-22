# トレースビューア

エンジンが動かした 1 ゲームを、アニメーションで再生する。**ルールは Lean だけにあり、画面は表示だけをする。**

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
| 通信方式 | 標準入出力で Lean の子プロセスとつなぎ、Python の薄い橋渡しが localhost の HTTP にする。Lean 側は JSON を読まず、「`start SEED 席`」「`act 番号`」の 1 行だけを読む（答えは、直前の合法手の一覧の番号で送る） |
| 状態を丸ごと送るか | 手ごとに、トレースと同じ形の状態を丸ごと送る（`state.new` で、初めて現れたオブジェクトだけを足す）。差分は使わない |
| `Event` に Rune Pool と Exhaust の変化を足すか | 足さない。今までどおり、状態の差から描く |
| 操作する席 | 画面で選ぶ（P0 だけ・P1 だけ・両方）。もう一方は `demoAnswer` |

**橋渡しの安全**: `127.0.0.1` だけで待ち受け、Host と Origin を確かめ、POST は `application/json` だけを受ける。ゲームは 1 つ。ブラウザからは Artifact のページのように外へ通信できない場所では動かない（ライブ操作の欄は、橋渡しが見つかったときだけ出る）。

**まだ無いもの**: 時計・ジャッジ・Limited の設定の選択（今はデモのデッキを Core Rules で動かす）、2 人とも人のときの隠れ情報（相手の手札が見える）、カードを指す操作（今は答えを文のボタンで選ぶ）。

## 次の段階

時計・ジャッジ・Limited の設定をライブ操作で選べるようにする。カードや Battlefield を直接クリックして答える。
