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
- 公式ギャラリーを正とする。2026-11-21 の取得では、ページに入っている印刷は 1,408 件で、報告された総数は 1,416 件（8 件が欠ける）。
- supertype は Riftcodex で補うか、代替テキスト（"Riftbound Unit: ..."）を解析して補う。
- エラッタは公式のエラッタ記事から手で反映する。

## 3. 取り込みのパイプライン

```text
scripts/fetch.py      公式ギャラリーから取得し、日付つきのスナップショット JSON を作る
scripts/normalize.py  正規化: 型の補正、supertype の補完、印刷違いを論理カードに束ねる、エラッタの適用
scripts/gen_lean.py   RiftboundCards/<Set>.lean の生成ブロックを更新し、新しいカードの雛形を足す（§4）
                      --check を付けると書き換えずに差分の有無だけを返す（全体の検証 verify.sh 用）
scripts/coverage.py   実装状況の表を生成（docs/ に出す）
```

- パイプラインは、解釈器より前に作る（[roadmap.md](roadmap.md) M3b）。IR の形を、実際のカードの転記で確かめるためである。
- Python は `uv` で管理し、`uv run` で実行する。依存の追加は `uv add` で行う。
- Lean からビルド時に JSON を読む方式は取らない。標準的な手順が確立しておらず、ビルドの再現性とキャッシュが複雑になるためである。
- 取得したスナップショット JSON と、生成ブロックを含む `RiftboundCards/<Set>.lean` はコミットする。差分をレビューでき、ビルド時にネットワークが要らない。
- 全体の検証（`scripts/verify.sh`。[lean-guidelines.md §7](lean-guidelines.md#7-作業の単位とローカルでの検証)）の中で `gen_lean.py --check` を実行し、生成ブロックがスナップショットと一致していることを確かめる。検証はローカルで行う。
- 公式ギャラリーからの取得は、手で実行する。新しいセットやエラッタの告知があったときに `fetch.py` を実行し、スナップショットとの差分を確かめる。対象は新カード、文面の変更、エラッタ。定期実行は、CI を置くことになったときに考える。
- **論理カードの同一性**:
  - キーは「名前 + subtitle」。名前は subtitle を含めた全体で 1 つである（CR 103.3.b, 132）。
  - ルール文面のハッシュは、キーに含めない。変更の検出にだけ使う。キーに含めると、エラッタのたびに別のカードになり、手書きの効果との対応が切れる。
  - 印刷のキーは `publicCode`（例: `OGN-029/298`）か `id`。`collectorNumber` は一意でない。
- **`CardId` の決め方**:
  - 最初の印刷の `publicCode` から、通し番号の分母を除いたもの（例: `OGN-029`）を `CardId` にする。
  - 「最初の印刷」は、発売日が最も早い印刷とする。同じ日なら §1 の表で上にある弾、その中では通し番号が最も小さい印刷とする。
  - 一度決めた `CardId` は変えない。エラッタや再録があっても同じ値を使う。
  - 再録されたカードは、同じ `CardId` の印刷として列挙する。定義は、最初の印刷の弾のファイルに置く（§4.1）。
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
  sets       : List SetCode        -- 印刷された弾（TR 601.2 の合法性の判定に使う）
  abilities  : List Ability        -- Passive / Replacement / Activated / Triggered（CR 361）
  spellEffect : Option EffectDef   -- Spell の選択の宣言と、解決するときに実行する指示（CR 355, 359.3）
  status     : ImplStatus          -- todo / drafted / partial / full（roadmap.md 末尾）
```

- `keywords` と `abilities` は別に持つ。キーワードの意味は `abilities` に書き込まず、実効のキーワードから導出する（design.md §7.4）。
- `EffectDef` は「選択の宣言 + 本体」の組である。プレイ時に選ぶもの（対象枠、モードなど）を宣言に並べ、本体の `Effect` からは番号で参照する（design.md §7.2）。能力の効果も同じ形で持つ。

### 4.1 ファイルの構成: 1 弾 1 ファイル

- **1 つの弾（セット）を 1 つのファイルにする**: `RiftboundCards/Origins.lean`、`RiftboundCards/Spiritforged.lean` など。namespace は `RiftboundCards.Origins` のように弾ごとに分ける。
- ファイルの中に、論理カード 1 種ごとに次の 2 つを並べる。
  1. **生成ブロック**（`-- BEGIN GENERATED <publicCode>` 〜 `-- END GENERATED`）: 生成スクリプトが管理する。中身は、公式文面を入れた docstring と、メタデータ（`CardMeta`: 名前、型、コスト、Might、タグ、印刷されたキーワード）。
  2. **手書きの部分**: 生成ブロックの直後に置く。効果（`abilities`、`spellEffect`）と実装状況を書く。生成スクリプトはここに触れない。
- 公式文面は、コメントではなく docstring に入れる。理由は次の 3 つ。
  - エディタのホバー表示と API ドキュメントで見える。
  - docstring の必須チェック（`linter.missingDocs`）を満たす。
  - スクリプトで抽出して、スナップショットと照合できる。
- showcase などの印刷違いは別のカードにせず、同じ生成ブロックの中に印刷コードを列挙する。エラッタがあれば、現行の文面を載せ、出典を記す。
- 別の弾に再録されたカードは、最初の印刷の弾のファイルにだけ定義を置く。再録先の印刷コードは、その生成ブロックに列挙する（`CardId` の決め方は §3）。
- 生成スクリプトの動き:
  - 新しいカードには、生成ブロックと手書き部分の雛形（`status := .todo`）を足す。
  - 既存のカードは、生成ブロックだけを書き換える。
  - 文面が変わった（エラッタなど）カードは、検証スクリプトの検査で差分として現れるので、手書きの効果を見直すきっかけになる。
- カード文面のキーワードは `[Keyword]` の形で印がついているので、機械的に抽出できる。効果の文が無い「キーワードだけのカード」（調査時点で 63 種）は、生成だけで `full` にできる（完了条件の免除は roadmap.md 末尾）。
- 1 弾 1 ファイルを選んだ理由（2026-11-20 の計測）:
  - 200 枚を 200 ファイルに分けると、クリーンビルドは 52 秒（10 コア）。
  - 同じ 200 枚を 1 ファイルにすると 1.9 秒。
  - 時間の大半はファイルごとの固定費なので、ファイル数を弾の数（6〜7）に抑える。
- ファイルの長さの規約（[lean-guidelines.md §4.2](lean-guidelines.md#42-ファイル)）からは例外とする。エディタでの再検査が重くなったら、弾の中で分ける（例: `Origins/Part1.lean`）。
- カードのファイルは、効果 IR とカード定義（`Riftbound.Card`）だけを import する。エンジン全体やテスト用の DSL は import しない。シナリオテストは `RiftboundTest` に置く。
  - `custom` ハンドラも、この層の型（`Value` と `Effect`）だけで書ける。ハンドラは `GameState` を受け取らない（design.md §7.1）。

```lean
-- RiftboundCards/Origins.lean の一部（イメージ。IR の名前は design.md §7.2 の初期案）

-- BEGIN GENERATED OGN-029/298
/--
**Falling Star** — Spell · Fury · Cost 2 Energy + 2 Fury Power
Printings: OGN-029/298

> Deal 3 to a unit.
> Deal 3 to a unit.
-/
def fallingStar.meta : CardMeta :=
  { id := ⟨"OGN-029"⟩, name := "Falling Star", types := [.spell], domains := [.fury],
    cost := some { energy := 2, power := [.fury, .fury] }, keywords := [] }
-- END GENERATED

/-- Falling Star の効果。 -/
def fallingStar : CardDef :=
  { fallingStar.meta.toDef with
    spellEffect := some {
      -- プレイ時に選ぶ対象枠（CR 355）。本体からは番号で参照する
      choices := [.target .anyUnit, .target .anyUnit],
      body := .seq [
        .deal (.slot 0) (.const 3),
        .deal (.slot 1) (.const 3)] }
    status := .full }
```

- **実装では、識別子はカード名ではなく `cardId`**（`OGN_029.meta`、`OGN_029`）にした。メタデータの型は `CardMeta` ではなく `CardDef` そのもの（効果の欄が入るまで、手書きの部分は `def OGN_029 : CardDef := OGN_029.meta`）。
- [確認済] `fallingStar.meta` と `fallingStar` を同じ namespace に並べて定義する形は、`module` の下の v4.36.0 で通る。

- `Registry.lean` で、全カードと `custom` ハンドラを集めて `CardDB` を作る。一覧は生成スクリプトが作る。

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

- `ImplStatus` の定義は [roadmap.md](roadmap.md) の末尾にある（`todo` / `drafted` / `partial` / `full`。多人数の仕組みを待つカードは `partial` で、理由を `needs-M9` と書く）。
  - `drafted` は、効果を IR の値として転記しただけの状態である。解釈器とテストを作る前に、IR の形を実際のカードで確かめるために使う（roadmap.md M3b）。
- `custom` を使ったカードは、表で区別する。`custom` はハンドラ表への参照で、ハンドラは解釈器が評価した値を受け取り、IR を組み立てて返す（design.md §7.1）。
- `scripts/coverage.py` がセットごとの表を作る。表には件数、IR で書けた割合（`drafted` 以上）、`full` の割合、`custom` の一覧、テストの有無を出す。
- 1 枚のカードの完了条件は [roadmap.md](roadmap.md) の末尾を参照。

## 7. モデルにとって難しいカード（先に設計で考慮しておくもの）

| 分類 | 例（カード名と、効果の要約） | 必要な仕組み |
|---|---|---|
| コピー | Mirror Image（Reflection トークンを出し、Unit のコピーにする）、Svellsongur（Attach 先の文をコピーする）、Heimerdinger, Inventor（味方の Exhaust 能力をすべて持つ。カードごとに写した能力で、近似した） | Copy 層（479.1）、能力の付与 |
| Spell の Control 奪取 | Mystic Reversal（Spell の Control を得て、選択をやり直せる） | Making New Choices（750）。Control の奪取は `takeControl` で書けた。選び直しは、まだ無い |
| 置換 | Seraphic Wyvern（Channel を 1 枚増やす）、Smite（死ぬ代わりに Banish）、Ki Barrier（ダメージを防ぐ）、Otterpus（早いターンの得点を draw に置換） | 置換効果（367-375）、Prevent（438） |
| 誘発回数の倍化 | Karthus, Eternal（Deathknell がもう一度誘発する）、Blue Sentinel（Hold 効果がもう一度誘発する） | 誘発回数の hook |
| ルールを変える Passive | Aspirant's Climb（勝利に必要な点 +1）、The Grand Plaza（条件を満たすと勝利）、Forgotten Monument（3 ターン目まで Score できない）、Dune Surfer（Tank を無視） | design.md §7.3 の hook |
| 追加ターン | Time Warp | 734-738 |
| Control の変更 | Possession（Control を得て Recall する） | Controller の層（479.2）、Contested（190.3.a.2） |
| 隠れ情報 | Hidden 関連、相手の手札を公開させる効果、Main Deck の一番上を参照する効果 | Facedown Zone、Reveal（425）、Privacy（128） |
| 可変コスト | Rhasa the Sunderer（Trash の枚数だけ安くなる）、Atakhan（追加コストで kill した Unit のコストだけ安くなる） | コスト計算（356）、支払いの順序（357） |
| 構築とゲーム外への参照 | Neeko, Blending In（構築時に Legend を追加で選ぶ） | 103.1、Legend Zone |
| 名前の指定 | Fallen Feline（Spell の名前を指定し、それを禁止する） | 解決時に論理カード ID を選び、発生源のオブジェクトに記録する（759-762） |
| 導出値への誘発 | Renekton, Brute（Might が 10 以上になったとき）、Grand Duelist（Mighty になったとき） | 状態変化の検出（709）。処理の 1 歩の前後で実効特性を比べる（design.md §5.4） |
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
2. `scripts/fetch.py` でスナップショットを取得し、`gen_lean.py` で `RiftboundCards/<Set>.lean` を作る（生成ブロックと、手書き部分の雛形）。
3. 構文だけの転記で、新しいカードが今の IR で書けるかを確かめる（実装状況は `drafted`）。書けなかった文から、足りない語彙を洗い出す。
4. 新しいキーワード（§8）と、新しいプリミティブ・hook を IR に足す。
5. カードの効果に意味を与え、シナリオテストを書く（`full` にする）。
6. 公式 FAQ と裁定を、回帰テストにする。
7. カバレッジ表を更新する。

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
- **決定（design.md §12 Q1）**: カードの公式文面（英語）をコミットする。あわせて次を守る。
  - **免責文は必須。** リポジトリ直下の `README.md` に、Legal Jibber Jabber が求める次の文を置く。

    > riftbound-lean4 was created under Riot Games' "Legal Jibber Jabber" policy using assets owned by Riot Games. Riot Games does not endorse or sponsor this project.

  - `NOTICE` に、カード名・カード文面・ルール文書は Riot Games の著作物で、Apache-2.0 はコードにだけ適用されることを書く。
  - 非商用にする。
  - カード画像とフレーバーテキストは扱わない。
  - 必要なら、Developer Portal を通じて Riot に確認する。
