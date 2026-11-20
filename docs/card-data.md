# カードデータと効果 IR

カードをどこから取り込み、どう Lean のデータにし、どう効果 IR に落とすかの方針。効果 IR そのものの設計は [design.md §7](design.md#7-効果-ir深い埋め込み) を参照。

## 1. カードプールの現状（2026-11-20 時点）

| セット | コード | 通し番号上の枚数（collector number の最大値） | 英語版の発売 | 主な新しい仕組み |
|---|---|---|---|---|
| Origins | OGN | 298 | 2025-10-31 | 基本のキーワード（Accelerate、Action、Assault、Deathknell、Deflect、Ganking、Hidden、Legion、Reaction、Shield、Tank、Temporary、Vision） |
| Proving Grounds | OGS | 24 | 2025-10-31 | 構築済みデッキ 4 つ |
| Spiritforged | SFD | 221 | 2026-02-13 | Equipment / Equip、Quick-Draw、Repeat、Weaponmaster、Gold トークン |
| Unleashed | UNL | 219 | 2026-05-08 | XP / Hunt / Level、Ambush、Backline、Predict、Battlefield トークン |
| Vendetta | VEN | 166 | 2026-07-31 | Empower / Empowered、Flow、Burn、Unit-Gear |
| Radiance | RAD | 167 | 2026-10-23 | Deploy、Disarm、Show Off、Equipment が Unit になる、Bomb トークン |
| Legacy（予告） | LGC | 239 | 2027-01-29 | 新しい文面テンプレート（"When I enter"、トークンの "Create" など） |

- 公式ギャラリーには 1,416 件の印刷がある。showcase などの印刷違いを除くと、論理カードは約 1,100 種。
- Proving Grounds 以外の英語版の発売日のうち一部は、二次情報による。The Reckoning（Set 7）の発売日には、公式資料の間で食い違いがある。
- 2026-11-20 時点の分析では、カード効果に乱数（random、shuffle）を含むものは無い。

## 2. データ源

| 源 | 形式 | 長所 | 注意点 |
|---|---|---|---|
| **公式カードギャラリー**（https://playriftbound.com/en-us/card-gallery/ ） | ページ HTML 内の `__NEXT_DATA__`（JSON）。カード一覧は `props.pageProps.page.blades[type=="riftboundCardGallery"].cards.items[]` | 一次情報。Radiance まで揃っている | supertype（Champion / Signature）の欄が無い。Radiance の 15 枚は型の欄が空、5 枚は型が誤っている（代替テキストで照合が必要）。文面は印刷時のもので、エラッタは反映されない。公開された API ではなく、予告なく変わりうる |
| Riftcodex API（https://api.riftcodex.com ） | REST / JSON | `supertype` がある。認証が要らない | 2026-11-20 時点で Radiance が未収録。ライセンスの明記が無い |
| OpenRift API（https://openrift.app/developers ） | REST / JSON | Radiance を収録。ルール文書の API もある | 軽い利用に限るよう求めている。サイトのコードは AGPL-3.0。カードの権利は Riot にある |
| Riot Developer Portal | 承認制の API | 公式 | アプリの登録が必要。ポリシーは §10 を参照 |
| コミュニティのダンプ（slimtreble、Dystorted888、sstmminer など） | JSON / CSV / SQLite | 取得スクリプトの参考になる。エラッタの記録（93 件）もある | カードデータ自体は再配布の権利を与えていない |

**方針**:
- 公式ギャラリーを正とする。
- supertype は Riftcodex で補うか、代替テキスト（"Riftbound Unit: ..."）を解析して補う。
- エラッタは公式のエラッタ記事から手で反映する。

## 3. 取り込みのパイプライン

```text
scripts/fetch.py      公式ギャラリーから取得し、日付つきのスナップショット JSON を作る
scripts/normalize.py  正規化: 型の補正、supertype の補完、印刷違いを論理カードに束ねる、エラッタの適用
scripts/gen_lean.py   RiftboundCards/<Set>/Meta.lean を生成（コミットする）
scripts/coverage.py   実装状況の表を生成（docs/ か CI のサマリーに出す）
```

- Python は `uv` で管理し、`uv run` で実行する。依存の追加は `uv add` で行う。
- Lean からビルド時に JSON を読む方式は取らない。標準的な手順が確立しておらず、ビルドの再現性とキャッシュが複雑になるためである。
- 生成物（`Meta.lean`）はコミットする。差分をレビューでき、ビルド時にネットワークが要らない。
- 定期実行の CI（週 1 回など）で取得し、スナップショットとの差分を報告する。対象は新カード、文面の変更、エラッタ。
- **論理カードの同一性**:
  - キーは「名前 + subtitle」と、ルール文面のハッシュの組。
  - 印刷のキーは `publicCode`（例: `OGN-029/298`）か `id`。`collectorNumber` は一意でない。
- 外部サービスに送る User-Agent に、個人の連絡先を入れるかどうかはユーザーが決める。既定では入れない。

## 4. Lean 側の表現

```lean
/-- 論理カード 1 種の定義。 -/
structure CardDef where
  id         : CardId              -- 論理カードの ID
  name       : String
  subtitle   : Option String
  types      : List CardType       -- 複数の型がありうる（CR 177）
  supertypes : List Supertype
  tags       : List Tag
  domains    : List Domain
  cost       : Option Cost         -- Energy と Power
  might      : Option Int
  mightBonus : Option Int          -- Equipment（CR 137）
  keywords   : List KeywordInst    -- 印刷されたキーワード（パラメータつき。design.md §7.4）
  abilities  : List Ability        -- Passive / Replacement / Activated / Triggered（CR 361）
  spellEffect : Option Effect      -- Spell が解決するときに実行する指示（CR 359.3）
  status     : ImplStatus          -- todo / partial / full（roadmap.md 末尾）
```

- `keywords` と `abilities` は別に持つ。キーワードの意味は `abilities` に書き込まず、実効のキーワードから導出する（design.md §7.4）。
- `Meta.lean`（生成）は、メタデータとキーワードだけを持つ既定値（`status := .todo`）を定義する。
  - カード文面のキーワードは `[Keyword]` の形で印がついているので、機械的に抽出できる。
  - 効果の文が無い「キーワードだけのカード」（調査時点で 63 種）は、生成だけで `full` にできる（完了条件の免除は roadmap.md 末尾）。
- 効果は、セットごとのファイルに手で書く。生成した既定値を上書きする形にする。

```lean
-- RiftboundCards/Origins/FallingStar.lean（イメージ。IR の名前は design.md §7.2 の初期案）
def fallingStar : CardDef :=
  { Meta.fallingStar with
    spellEffect := some (.seq [
      .deal (.choose 0 .anyUnit) (.const 3),
      .deal (.choose 1 .anyUnit) (.const 3)])
    status := .full }
```

- `Registry.lean` で、全カードと `custom` ハンドラを集めて `CardDB` を作る。生成スクリプトが一覧を作る。

## 5. 文面のパターンと IR への写像

調査では、1,779 行の能力文が 1,171 種類のテンプレートに分かれた。上位 100 種類のテンプレートで約 40% を覆う。残りは合成で表す。

| パターン（文面の型） | 出現の目安 | IR |
|---|---|---|
| ダメージを与える（"Deal N to ..."） | 多い | `deal selector amount` |
| 引く / 捨てる / Burn / Predict | Draw は 162 種 | `draw`、`discard`、`burn`、`predict` |
| このターン +N Might | 127 種 | `grant sel (.might n) .thisTurn` |
| Kill / Banish / Recall / 手札に戻す / Stun / Counter | Kill は 83 種 | 各プリミティブ |
| Move / Ready / Exhaust / Attach | Move は 114 種、Ready は 132 種 | 各プリミティブ |
| トークンを出す | 82 種 | `create token` |
| 誘発: プレイ時、攻撃時、Conquer / Hold、移動時、Deathknell | "When you play me" だけで 128 種 | `Ability.triggered` と `Trigger` |
| 条件: 〜を Control しているなら、Victory Score までの残り点、Level、Empowered | — | `Condition` |
| 選択: choose one、up to N、for each | choose one は 22 種、for each は 47 種 | `chooseOne`、`Selector`、`Amount.forEach` |
| 追加コスト、割引、代替コスト（Flow、コストを無視） | 追加コストは 46 種 | `Cost` と `StaticMod.costMod` |
| Legend の起動能力（Exhaust: ...） | Legend ごと | `Ability.activated` |
| Battlefield の能力（here を参照する） | Battlefield ごと | `Selector.here` |

## 6. 実装状況の管理

- `ImplStatus` の定義は [roadmap.md](roadmap.md) の末尾にある（`todo` / `partial` / `full`。多人数の仕組みを待つカードは `partial` で、理由を `needs-M9` と書く）。
- `custom` を使ったカードは、表で区別する。`custom` はハンドラ表への参照で、ハンドラは状態を見て IR を組み立てて返す（design.md §7.1）。
- `scripts/coverage.py` がセットごとの表を作る。表には件数、`full` の割合、`custom` の一覧、テストの有無を出す。
- 1 枚のカードの完了条件は [roadmap.md](roadmap.md) の末尾を参照。

## 7. モデルにとって難しいカード（先に設計で考慮しておくもの）

| 分類 | 例（カード名と、効果の要約） | 必要な仕組み |
|---|---|---|
| コピー | Mirror Image（Reflection トークンを出し、Unit のコピーにする）、Svellsongur（Attach 先の文をコピーする）、Heimerdinger, Inventor（味方の Exhaust 能力をすべて持つ） | Copy 層（479.1）、能力の付与 |
| Spell の Control 奪取 | Mystic Reversal（Spell の Control を得て、選択をやり直せる） | Making New Choices（750） |
| 置換 | Seraphic Wyvern（Channel を 1 枚増やす）、Smite（死ぬ代わりに Banish）、Ki Barrier（ダメージを防ぐ）、Otterpus（早いターンの得点を draw に置換） | 置換効果（367-375）、Prevent（438） |
| 誘発回数の倍化 | Karthus, Eternal（Deathknell がもう一度誘発する）、Blue Sentinel（Hold 効果がもう一度誘発する） | 誘発回数の hook |
| ルールを変える Passive | Aspirant's Climb（勝利に必要な点 +1）、The Grand Plaza（条件を満たすと勝利）、Forgotten Monument（3 ターン目まで Score できない）、Dune Surfer（Tank を無視） | design.md §7.3 の hook |
| 追加ターン | Time Warp | 734-738 |
| Control の変更 | Possession（Control を得て Recall する） | Controller の層（479.2）、Contested（190.3.a.2） |
| 隠れ情報 | Hidden 関連、相手の手札を公開させる効果、Main Deck の一番上を参照する効果 | Facedown Zone、Reveal（425）、Privacy（128） |
| 可変コスト | Rhasa the Sunderer（Trash の枚数だけ安くなる）、Atakhan（追加コストで kill した Unit のコストだけ安くなる） | コスト計算（356）、支払いの順序（357） |
| 構築とゲーム外への参照 | Neeko, Blending In（構築時に Legend を追加で選ぶ） | 103.1、Legend Zone |
| 名前の指定 | Fallen Feline（Spell の名前を指定し、それを禁止する） | 名前を値として持つ |
| 導出値への誘発 | Renekton, Brute（Might が 10 以上になったとき）、Grand Duelist（Mighty になったとき） | 状態変化の検出（709） |
| 回数つきの遅延誘発 | Fanfare（このターン、次の 3 回の Unit のプレイで引く） | Delayed 能力（390-393）と回数 |
| 多人数向けの文 | Whirlwind（次のプレイヤーから順に）、2v2 の "you or an ally" | 手番順の走査、味方（740.1） |

## 8. 新しいキーワードを追加する手順

1. CR の該当規則を読み、[rules-model.md §19](rules-model.md#19-キーワード805-83228-個) の表に追記する。
2. `Keyword` 型にコンストラクタを追加する。パラメータがあれば持たせる。
3. 意味を与える。誘発型・起動型なら能力の列への展開、Passive 型ならエンジンの hook（design.md §7.4）。
4. 意味の補題を 1 つ以上書く（例: Assault X は Attacker である間だけ +X）。
5. 生成スクリプトのキーワード抽出に、そのキーワードを追加する。
6. そのキーワードだけを持つテスト用のカードで、シナリオテストを書く。

## 9. 新しいセットを追加する手順

1. 公式のパッチノートと、更新された Core Rules を確認する。ルールが変わっていれば、先に [design.md §9](design.md#9-ルールとカードの版管理) の手順で反映する。
2. `scripts/fetch.py` でスナップショットを取得し、`gen_lean.py` で `Meta.lean` を生成する。
3. 新しいキーワード（§8）と、新しいプリミティブ・hook を IR に足す。
4. カードの効果を書き、シナリオテストを書く。
5. 公式 FAQ と裁定を、回帰テストにする。
6. カバレッジ表を更新する。

## 10. 権利面の注意（法的助言ではない）

- **Riot の Riftbound 開発者ポリシー**（https://developer.riotgames.com/policies/riftbound ）:
  - 承認しない用途として「自動ルール適用によるデジタルゲームプレイ」を挙げている。
  - ゲームをシミュレートするアプリの収益化は認めていない。
  - カードは公式の英語テキストで表示することを求めている。
  - これらは主に、API を使ってプレイヤーにサービスを提供するプロダクト向けの規定である。研究目的の形式化リポジトリへの当てはめは不明。
- **Riot の Legal Jibber Jabber**（https://www.riotgames.com/en/legal ）:
  - 無料・非商用のファンプロジェクトを、取り消し可能な許諾として認めている。
  - 所定の免責文の表示を求めている。
- このリポジトリは **公開** で、コードは Apache-2.0 である。
- **推奨**:
  - コードのライセンス（Apache-2.0）は、カード由来のデータ（名前・文面）には及ばないと README に明記する。
  - 非商用とし、Riot が推奨・後援していない旨の免責文を README に置く。
  - カード画像とフレーバーテキストは扱わない。
  - カード全文（英語の文面）をリポジトリにコミットするかは、ユーザーが判断する（design.md §12 Q1）。
    - 慎重にする場合: スナップショット JSON はコミットせず、取得スクリプトだけを置く。`Meta.lean` には名前・数値・キーワードだけを入れ、文面は入れない。
  - 必要なら、Developer Portal を通じて Riot に確認する。
