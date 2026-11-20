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

## 次の段階

画面からボタンで答えを選び、Lean を呼ぶライブ操作は、まだ作っていない。ブラウザからは Artifact のように外へ通信できる場所でないと Lean に届かないので、ローカルの HTML と stdin/stdout、または localhost の薄い橋渡しで作る。
