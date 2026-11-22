# Riftbound ルールの形式化メモ（CR 2026-10-09 準拠）

Riftbound の公式 Core Rules を、Lean で形式化する観点で整理したもの。設計方針は [design.md](design.md)、実装の順序は [roadmap.md](roadmap.md) を参照。

> **これは公式ルールの代わりではない。** 規則文は要約であり、逐語引用は避けている。厳密な文言は、必ず公式 PDF を規則番号で引くこと。

## 0. 出典と版

| 項目 | 内容 |
|---|---|
| 正とする文書 | Riftbound Core Rules, **Last Updated: 2026-10-09**（142 ページ）。公式 Rules Hub（https://playriftbound.com/en-us/rules-hub/ ）からリンクされた PDF |
| 発効 | 2026-10-16（Radiance Pre-Rift から）。Radiance パッチノートが 2026-10-09 に公開された |
| 版番号 | 公式の版番号は無く、日付だけが版を表す。本リポジトリでは「CR」と書けばこの版を指す |
| 古い二次資料 | hyperlinked 版（jeff425）と riftbound.gg/rules は 2026-07-16 版（Vendetta 期）であり、**規則番号の根拠に使わない** |
| 補助資料 | 各セットのパッチノート、Radiance Rules FAQ（2026-10-27）。パッチノートは「新しい Core Rules がノートより優先する」と述べている |
| 今後 | 2027-01 の Legacy で全面的な書式刷新が予告されている（規則番号が変わる見込み） |
| Tournament Rules | 大会では Tournament Rules（2026-10-09 版）が Core Rules に優先する（TR 104.1）。形式化の範囲は [tournament-model.md](tournament-model.md) |

規則番号の引用形式: docstring やコメントに `(CR 323.4)` と書く。

## 1. 文書の構成

| 番号 | 章 | 主な内容 |
|---|---|---|
| 000-056 | Golden and Silver Rules | 規則の優先順位 |
| 100-206 | Game Concepts | デッキ構築 101、セットアップ 104-118、ゲームオブジェクト 119、カード 125、各カード種別 140-178、トークン 179、Control 188、勝利 193、Location 197、コスト 201 |
| 300-649 | Playing the Game | ターン 301、状態 307、Priority と Focus 311、フェイズ 314-317、Cleanup 318、Chain と Showdown 325、カードのプレイ 349、能力 360、ゲームアクション 408、移動 447、Recall 456、戦闘 461、得点 469、Layers 475、ゲームモード 483、投了 649 |
| 700-767 | Additional Rules | Buff 701、Mighty 706、Bonus Damage 712、Attach 716、Inactive 720、Dependent Keyword 726、XP 728、追加ターン 734、用語 739、Counter 741、Making New Choices 750、Untargetability 756、名前・型・Tag の指定 759（Tag の一覧は 763.1）、Ignoring Effects 764 |
| 800-832 | Keywords | キーワード 28 個（805-832） |

番号の付け方:
- 見出しも番号を 1 つ使う。
- 下位の階層は `.a`、`.1` のように英字と数字を交互に連ねる（例: 467.2.c.4.a）。
- 欠番は意図的なもの。
- PDF 内の相互参照には古いものが残っている（§21 参照）。

## 2. 黄金律と銀則（000-056）

| 規則 | 内容 | モデル化 |
|---|---|---|
| 002 | カードの記述がルールと根本的に矛盾するなら、カードが正しい | ルールの各所に hook を置き、カードが既定の動作を上書きできるようにする（design.md §7.3） |
| 051-053 | カード文面はこの規則に従って解釈する。"card" は Main Deck のカードを指す。自己参照は Unit / Legend が "I"、Gear / Spell が "this"、Battlefield が "here" | 効果 IR では、自己参照を `Selector.self` に正規化する |
| 054.1 | **Can't beats Can**: 禁止は許可に優先する | 制限（restriction）は許可（permission）より常に優先して判定する |
| 054.2 | 「only」と書かれた条件の外では行えない | 許可の条件として表す |
| 055 | できる範囲で実行し、不可能な指示は無視する。すべて不可能でも、プレイと解決は行われる | 解釈器は、不可能な指示を飛ばして続ける。エラーにはしない |
| 056 | 自分が Own するカードは、他プレイヤーの Non-Board ゾーンに入らない | `moveObj` の行き先を Owner のゾーンに正規化する |

## 3. デッキ構築とセットアップ

### 3.1 デッキ構築（101-103）

| 規則 | 要件 |
|---|---|
| 103.1 | カードやモードが、構築時の追加選択を求めることがある（例: Neeko で Legend を追加で 3 つ選ぶ） |
| 103.2 | Champion Legend 1 枚。Domain Identity は Legend のドメインで決まる（103.2.b） |
| 103.2.b.3-6 | 単一ドメインのカードは Identity にそのドメインがあれば可。複数ドメインのカードは全ドメインを含む場合だけ可。ドメインなしはどこでも可。ゲーム中の効果で Domain を無視してデッキに加えたカードは、Identity に適合するとみなす（103.2.b.6） |
| 103.3 | **Main Deck は 40 枚以上**。Chosen Champion と、Unit・Gear・Spell で構成する |
| 103.3.a | Chosen Champion: Champion Tag が Legend と一致する Champion Unit（Signature は不可）。同名の Champion Unit 全体を指す（103.3.a.3） |
| 103.3.b | 同名カードは 3 枚まで。Chosen Champion も数える。名前は subtitle を含めた全体 |
| 103.3.d | Signature カードは合計 3 枚まで。すべて Legend の Champion Tag を持つ |
| 103.4 | **Rune Deck はちょうど 12 枚**。Domain Identity に従い、Main Deck とは別にシャッフルする |
| 103.5 | Battlefield の枚数はモードが決める。2 枚以上必要な場合は、同名の Battlefield を入れられない（103.5.c） |
| 825 | Unique: 同名は 1 枚まで |

補足: Tournament Rules の Constructed では「Main Deck はちょうど 40 枚（Chosen Champion を含む）、名前の異なる Battlefield ちょうど 3 枚、サイドボード 10 枚以下」となっている（TR 402.1, 601）。Limited（Sealed / Draft）はさらに別の規則を持つ。本リポジトリでは両方に対応し、フォーマットごとの別の述語として持つ（[tournament-model.md §2](tournament-model.md#2-フォーマットとデッキの合法性)）。

### 3.2 セットアップ（110-118）

1. Champion Legend を Legend Zone に置く（111）。
2. Chosen Champion を Champion Zone に置く（112）。
3. モードの規定に従って Battlefield を用意する（113）。
4. Main Deck と Rune Deck を別々にシャッフルする（114）。
5. 公平なランダムな方法で手番順を決める。手番順は First Player から時計回りに繰り返す（115）。大会では、ランダムに決めたプレイヤーが先手か後手かを選ぶ（TR 407）。
6. 全員が 4 枚引く（116）。
7. 手番順にマリガンする: 最大 2 枚を脇に置き、同じ枚数を引き、脇に置いたカードを Recycle する（117）。
8. First Player がターンを始める（118）。

- 初期の Rune や Energy は無い。Rune は通常 Channel で場に出る。ほかに、効果で Create されるトークンの Rune がある（440.2.b.3, 185.2.e）。
- **偶然の決定**: シャッフル、手番順、Battlefield のランダムな選択（Duel 487.5、FFA3 489.5、FFA4 490.5、2v2 491.5.a。Match 488.5 はプレイヤーが選ぶ）、マリガンで Recycle するカードの順序（417.5）。

## 4. カードとゲームオブジェクト

### 4.1 分類（133）

| 区分 | 内容 |
|---|---|
| Main Deck のカード | Permanent（Unit、Gear）と Spell |
| Rune Deck のカード | Rune。Permanent ではない（161.1） |
| その他のカード | Battlefield、Legend |
| トークン | カードではない、独立した区分のゲームオブジェクト（185.1）。トークン性を失うことも、カードがトークンになることもない |
| 複数の型 | すべての型の性質を併せ持つ（177-178）。例: Unit-Gear。性質が排他的なときの優先は 178.1.a による。Unit を含むなら Might を持ち、exhausted で入り、Battlefield から Recall されない。Rune を含むなら Rune Deck へ Recycle される |

### 4.2 カードの属性

- **Supertype**（133.7）: Champion（Unit のみ）、Signature。
- **Tag**（133.8）: 原則としてルール上の意味を持たない。例外として Equipment tag は意味を持つ（150）。Tag の一覧は 763.1。
- **Domain**（134）: Fury、Calm、Mind、Body、Chaos、Order の 6 つ。
- **コスト**（131, 135.2.e）:
  - Energy は数値。
  - Power はドメインつきのシンボル。
  - `[A]` はどのドメインでも払える Power。
  - `[C]` はそのカード自身のドメインの Power。
- **Might**（143）:
  - 印刷値・基本値・実効値の 3 種類がある。単に Might と書けば実効値。
  - 負の Might は、参照時と戦闘ダメージの合計時には 0 として扱う。実際の値は負のまま（143.2.c）。
  - Mighty は Might が 5 以上であること（708）。盤面外では印刷値で判定する（711）。
- **名前**（132）: 「Short Name, Subtitle」の全体が名前。

### 4.3 種別ごとの性質

| 種別 | 性質 |
|---|---|
| Unit | 盤面に **exhausted** で入る（143.4。Accelerate で変えられる）。Standard Move を持つ（144）。ダメージは Unit ごとの値で、ゲームオブジェクトではない（142）。**致死ダメージ**は「0 でない量で、かつ Might 以上」（142.4.b）。他のものに Attach できない（143.5） |
| Gear | ready で入る（149.1）。通常は自分の Base にだけ出せる。例外は Deploy（830。Battlefield にだけ出せ、Base には出せない: 830.1.b）と Hidden。Attach されていない Unit でない Gear が Battlefield にあれば、Cleanup で Recall される（149.3, 323.6）。ただし Deploy を持つものは Recall されない（459.1, 830.1.b.3） |
| Spell | 自分のターンの Open State で、Showdown 外でプレイする（155）。解決後は Owner の Trash へ行く（359.3.d） |
| Rune | Main Deck のカードでも Permanent でもない。Recycle 先は Rune Deck（161.2.b） |
| Battlefield | ゲームオブジェクトであり、Location でもある。Kill も Move もできず、Permanent ではない（170-171） |
| Legend | Legend Zone に置く。Kill も Move もできない（174-175） |

### 4.4 トークン（179-187）

- Board と Chain の上にだけ存在できる。それ以外のゾーンに入ると、直後に消える（186.1）。
- コストは 0 として扱い、ドメインは無い。
- Controller は、トークンを生成した効果の Controller。
- 定義済みのトークン（187）: Recruit、Sprite、Sand Soldier、Mech、Gold（gear）、Reflection、Bird、Brush（battlefield）、Baron Pit（battlefield）、Tentacle、Shadow Clone、Bomb（gear）。

### 4.5 オブジェクトの同一性（124）

- **Non-Board ゾーンへ（から）移ったゲームオブジェクトは、新しいオブジェクトになる。** ダメージ、カウンター、付与されたキーワード、ステータスなど、一時的な修正はすべて失われる（124.1）。
- Base と Battlefield Zone は別のゾーンだが、その間の Move は Non-Board ゾーンを経由しないので、新しいオブジェクトにはならない（124, 448.1）。逆に、ゾーンを変えること自体は Move ではない（448.2）。
- ステータスの例（124.2）: Attached、Attacking、Buffed、Defending、Empowered、Exhausted、Facedown、Revealed、Stunned など。
- モデル: Non-Board ゾーンを出入りするたびに新しい ObjId を払い出す（design.md §5.1）。

### 4.6 Owner と Controller（127, 188-192）

- **Owner** はカードをゲームに持ち込んだプレイヤー。生成されたオブジェクトは、生成したプレイヤーが Owner になる（440.4）。
- **Controller**:
  - Play・Hide・Create したプレイヤー（191.2）。
  - Spell はプレイしたプレイヤー（191.3）。
  - 能力は、既定でその発生源の Controller。発生源が Non-Board ゾーンにあれば Owner（191.5）。
  - **Chain 上の能力の Controller は、発生源の Control が変わっても変わらない**（191.5.b）。
- **Battlefield の Control** は二値（支配されている / いない）。支配者がいないときは Turn Player が責任を持つ（190.6.b）。
- **Contested**（190.3）:
  - Battlefield に付く一時的なステータス。
  - その Battlefield を支配していないプレイヤーの Unit が、移動・プレイ・Control の変更でそこに来ると付く。
  - 現時点では、ゲーム効果からは参照できない（190.3.d）。

### 4.7 情報の公開度（128）

| 段階 | 見られる人 | 例 |
|---|---|---|
| Secret | 誰も見られない | Main Deck の順序 |
| Private | 盤面上なら Controller、それ以外なら Owner | 手札、伏せたカード |
| Public | 全員 | Base、Battlefield、Trash など |

Secret / Private なカードへの指示（型や性質を指定するもの）は、プレイヤーが実行を拒否できる。拒否した指示は不可能なものとして扱う（128.6）。モデルでは「拒否するか」を決定要求にする。

## 5. ゾーン（105-109）

| ゾーン | Board か | 所属 | 順序 | 公開度 |
|---|---|---|---|---|
| Base | Board（Location） | プレイヤーごと | なし | Public |
| Battlefield Zone | Board | 共有。各 Battlefield が Location | なし | Public |
| Facedown Zone | Board（Battlefield の副ゾーン。Location ではない） | Battlefield ごと。容量は既定で 1 で、効果で増減する。減ったら超過分を Trash に置く（107.3.b） | なし | ゾーンは Public、中身は Private |
| Legend Zone | Board（Location ではない） | プレイヤーごと | なし | Public |
| Chain | Non-Board | 共有。同時に 1 つだけ（330） | **あり** | Public |
| Trash | Non-Board | プレイヤーごと | なし | Public |
| Champion Zone | Non-Board | プレイヤーごと | なし | Public |
| Main Deck | Non-Board | プレイヤーごと | **あり**（Secret） | 枚数は Public |
| Rune Deck | Non-Board | プレイヤーごと | **あり**（Secret） | 枚数が Public かは未確認 |
| Banishment | Non-Board | プレイヤーごと | なし | Public |
| Hand | Non-Board | プレイヤーごと | なし | Private（枚数は Public） |

## 6. 資源（160-168, 356-357, 414-417, 430-431, 445）

- **Rune Pool**（166）: Energy と、ドメインつきの Power を入れる概念上の器。
  - **Main Phase の開始時と、各ターンの終了時に空になる**（167）。
- **Basic Rune**（164）: 常に次の 2 つの能力を持つ。どちらも Reaction で起動できる。
  - Exhaust して Energy を 1 Add する。
  - 自分自身を Recycle して、その Rune のドメインの Power を 1 Add する。
- **Channel**（431）:
  - Rune Deck の一番上の Rune を Base に出す。既定では ready で出る。
  - Rune が足りなければ、出せるだけ出す。Burn Out は起きない。
- **Exhaust / Ready**（415-416）: exhausted のゲームオブジェクトを Exhaust しても何も起きない（415.1.b）。ready の Unit を Ready しても何も起きない（416.1.b。文言は Unit に限っている）。ただし、コストとしての Exhaust は実行できる必要がある（415.4）。
- **Recycle**（417）:
  - 常に Owner の、対応するデッキの下に置く。
  - **Main Deck に同時に複数を戻すとき、順序はランダム**（417.5）。Rune Deck に同時に戻すときは、Owner が順序を選ぶ（417.5.a）。
- **Add**（430）: 資源を Rune Pool に加える。
  - 資源を Add する誘発・起動能力は、Chain に Pending として載り、**直ちに finalize して即座に解決する**（430.2, 337.2）。タスクの処理中や他の解決の途中でもそうなる。
  - Priority と Focus は動かない。進行中のタスクや FEPR の段は、その間一時停止する（430.2.a）。
  - Reaction を持つ Add 能力は、支払いが必要な場面ならいつでも起動できる（430.3）。
  - 資源を Add する **Spell** は、通常の Spell と同じタイミングで finalize・解決する（430.2.b）。
  - 「Chain を使わない」のは Move（448.3.c）と Applied Cost（204.4）であって、Add ではない。
- **Pay**（445）:
  - 払うかどうかは任意。払わなければ、その指示は Negate される。
  - カードや能力のコストを払う途中で拒否すると、プレイそのものが取り消される。
  - `[0]` は Pay を伴わず、拒否できない。
- **総コストの決定順**（356）:
  1. 基本コストの置換。"for [Cost]" は置換、"ignore" はそのコストを 0 にする。
  2. 追加コスト。必須のもの（Deflect を含む）と、任意のもの。
  3. 増加。
  4. 割引。要素ごとの割引を先に、総額への割引を後に。変動する割引の値はここで確定する。
  5. 総額の修正。
  6. Energy と Power は 0 未満にならない。
- **支払い**（357）: Energy と Power の合計を払う（357.1）。それに加えて、非標準のコストを任意の順に払う（357.2）。置換されたコストも支払い済みとして扱う（357.2.a）。
  - CR の文言は "In addition" で、Energy と Power を「先に」払うとは書いていない。
  - Radiance Rules FAQ は、Energy と Power を非標準コストより先に払う裁定を示している（Atakhan の例）。モデルでは FAQ の順序に従う。
- **XP**（728-733）: プレイヤーの資源。ゲームオブジェクトではなく、上限は無い。

## 7. ターン構造と状態（301-317）

### 7.1 フェイズ

| # | フェイズ / ステップ | 処理 | 規則 |
|---|---|---|---|
| 1 | Awaken | Turn Player が Control するものをすべて Ready する | 315.1 |
| 2 | Beginning / Beginning Step | 「Beginning Phase の開始時」の効果。Temporary はここで kill される（Scoring より前） | 315.2.a, 816 |
| 3 | Beginning / Scoring Step | Turn Player が、Control するすべての Battlefield を Hold する | 315.2.b |
| 4 | Channel | Rune を 2 枚 Channel する | 315.3 |
| 5 | Draw | 1 枚引く。Main Deck が空なら、Burn Out してから 1 枚引く | 315.4 |
| 6 | Main | 開始時に全員の Rune Pool を空にする。以降は自由。Neutral Open State で、Turn Player が Priority を持つ | 316 |
| 7 | Ending / Ending Step | 「ターン終了時」の効果 | 317.1 |
| 8 | Ending / Expiration Step | 特殊な Cleanup で、次の 3 つを挿入する: 全 Unit を Heal（3c）、「このターン」効果の失効（3d）、Rune Pool を空にする（3e）。途中で FEPR を経た項目があれば、ステップの最初に戻る | 317.2 |

- 各フェイズの中では、別段の定めがなければ行動の順序は自由（303）。
- Chain が無く、Turn Player が Discretionary Action を行わないなら、次へ進む（305）。

### 7.2 4 つの状態（307-310）

| | Chain なし（Open） | Chain あり（Closed） |
|---|---|---|
| Showdown / Combat なし（Neutral） | Neutral Open | Neutral Closed |
| Showdown / Combat あり（Showdown） | Showdown Open | Showdown Closed |

モデルでは Open / Closed を保存せず、Chain の有無から導出する。

### 7.3 Priority と Focus（311-313）

- **Priority** は高々 1 人が持つ。Discretionary Action を行える唯一の権利である（312）。
- Priority を得る場面（312.2）:
  - Neutral Open での自分の Main Phase
  - Showdown で Focus を得たとき
  - Closed で、すべての Pending が finalize された後に、自分が次に解決される項目の Controller であるとき
  - Closed で、前のプレイヤーがパスしたとき
- **Focus** は Showdown Open で行動する許可（313）。
  - Focus を得ると Priority も得る。
  - Priority をパスしても Focus は残る。
  - Neutral では誰も Focus を持たない。

### 7.4 ゲームアクションの性質（303, 408-412）

- ゲームアクションは 1 つずつ、完全に実行する。同時には実行しない（303.1-2）。
  - ただし、1 つのアクションが複数のオブジェクトに作用した結果のイベントは同時（370.1.a.2）。
  - 同時に起きたものは、Turn Player から手番順に整列する（303.2.a）。
- **Discretionary Action** は自分のターンの Neutral Open でいつでも行える。**Limited Action** は指示されたときだけ行える（411）。
  - ただし、Showdown では Focus を持つプレイヤーも Discretionary Action を行える（313.1）。411.1.a の文言とは揺れがあるので、両方を満たすように実装する。
- **Responsibility**（412）: アクションの責任者は高々 1 人。「you が〜したとき」は、その人が責任を持つアクションで誘発する。

## 8. Cleanup（318-324）

**発生する時点**（319）:
- Open と Closed の切り替わり
- フェイズの切り替わり
- Pending の追加、または finalize
- Chain からの項目の除去
- Board への出入り
- ステータスの変化
- Move の完了

**制約**（320-322）:
- Cleanup 中は finalize も解決も行わず、Priority も Focus も動かない。
- 解決中は Cleanup を行わない。
- **状態が変わらなくなるまで繰り返す**（322）。

**手順**（323）:

| 手順 | 規則 | 内容 |
|---|---|---|
| 1 | 323.1 | Victory Score 以上で、かつ全対戦相手より多い得点のプレイヤーが勝つ |
| 2 | 323.2 | 戦闘中なら、Attacker / Defender の指定を付ける・外す |
| 3a | 323.4 | 致死ダメージを負った Unit を kill し、Owner の Trash に置く |
| 4 | 323.5 | Open で、Showdown も Combat も無く、自分の Unit がいない Battlefield の Control を失う |
| 5 | 323.6 | Recall: Battlefield 上の、Attach されていない Unit でない Gear と、Unit でない Rune。他人の Base にある、Attach されていない Permanent と Rune。あわせて、Battlefield の Controller と異なるプレイヤーの Hidden カードを Trash に送る（323.6.a） |
| 6 | 323.7 | Contested で Combat の無い Battlefield に、Showdown を Staged にする。Contested が続き、Contested を付けたプレイヤーの Unit がいる間は Staged のまま（323.7.a） |
| 7 / 7a | 323.8-9 | Contested で対立する Unit がいる Battlefield に、Combat を Staged にする。対立が消えたら取り消す |
| 8 | 323.10 | Contested を付けたプレイヤーの Unit も、Showdown / Combat も無い Battlefield から Contested を外す。その結果、未支配の Battlefield に Unit が残っていれば、その Unit の Controller が改めて Contested を付ける（323.10.a） |
| 9 | 323.11 | Neutral Open なら、Turn Player が「Staged な Showdown があり、Combat は Staged でない」Battlefield を 1 つ選んで、Showdown を開始する |
| 10 | 323.12 | Neutral Open なら、Turn Player が Staged な Combat を 1 つ選んで開始する |
| 10a | 323.13 | Showdown Open で、戦闘でない Showdown の場所に Combat が Staged されたら、その Showdown を Combat Showdown にする |

**特殊 Cleanup**（324）:
- Combat Cleanup（468.1）と Expiration Step（317.2）は、手順を挿入した Cleanup を 1 回だけ行う。
- そこから再び Cleanup が必要になったら、通常の Cleanup を行う。

## 9. Chain と HOT FEPR（325-340）

- **Chain** は Non-Board ゾーンで、同時に 1 つだけ存在する。項目が 1 つでもあれば Closed になる。
- 項目は **Pending** として加えられ、プレイ手順を終えると **Finalized** になる（329）。
- **HOT FEPR**（334）: Handle Outstanding Tasks（未処理タスクの処理）、続いて Finalize → Execute → Pass → Resolve。

| 段 | 規則 | 内容 |
|---|---|---|
| Finalize | 337 | 最も古い Pending の Controller が、プレイ手順を完了させる。Priority は渡さない。**Unit・Gear・Add 能力は finalize 直後に即解決**（337.2） |
| Execute | 338 | Priority を持つプレイヤーが、タイミングの合うカードか能力をプレイするか、パスする |
| Pass | 339 | 全員が続けてパスしたら Resolve へ。そうでなければ次のプレイヤーへ |
| Resolve | 340 | **最も新しい Finalized 項目を解決する（後入れ先出し）**。Chain が空になったら Open へ |

- Showdown 中に Chain が空になったら、Focus は次のプレイヤーに移る。例外は、Chain が誘発能力か Add 能力で始まった場合（340.2.a, 346.1）。

## 10. Showdown（341-348）

- **開始**: Neutral Open の Cleanup で、Turn Player が Staged な Showdown を選ぶ（323.11, 344）。戦闘の場合は、Combat の最初のステップとして開く（344.1）。
- **最初の Focus**: Contested を付けたプレイヤー（345）。Combat Showdown では次の 2 通りがある。
  - Combat が Showdown とともに開いた場合: Attacker が Focus を得る（466.2.c.1.a）。
  - 戦闘でない Showdown の進行中に Combat になった場合: その時点の Focus の保持者が、そのまま保持する（466.2.c.1.b）。
- **進行**: Focus を持つプレイヤーが、タイミングの合うカードや能力をプレイするか、パスする（347）。全員が続けてパスしたら閉じる（348）。
- **戦闘でない Showdown の終了**: Unit が残っているプレイヤーが 1 人だけで、かつそのプレイヤーがまだその Battlefield を Control していなければ、Control を確立する。そのプレイヤーが今ターンその Battlefield をまだ Score していなければ Conquer になる（348.2）。

## 11. カードのプレイ（349-359）と対象

### 11.1 6 つの段

| 段 | 規則 | 内容 |
|---|---|---|
| 1 | 354 | Chain に移す（Pending、Closed になる） |
| 2 | 355 | 選択: 任意の追加コストを払うか、Unit のプレイ先、モード、移動先、対象 |
| 3 | 356 | 総コストを決める（§6） |
| 4 | 357 | コストを支払う。Reaction の Add 能力をここで使える |
| 5 | 358 | 合法性を確認する: 選択、支払い、不正な状態にならないか、タイミングの許可。**失敗したら、行った処理をすべて取り消す**（358.5） |
| 6 | 359 | 最終化: Permanent は Board に出る（Unit は exhausted で）。Spell は Finalized として Chain に残る |

### 11.2 タイミング

- **既定**: 自分のターン、Neutral Open、Priority を持っているとき。
- **Action**（806）: Showdown 中にも行える（相手のターンでも可）。
- **Reaction**（813）: Action の許可に加えて、Closed 中にも行える。
- 「プレイされた」の扱いは、参照する側で異なる。
  - **誘発能力**（"When you play ..."）は、そのカードの解決が終わった時点で誘発する。Counter されたカードでは誘発しない（420.4.a.1, 426.1.b）。
  - **誘発でない参照**（Legion の条件、コストの条件など）は、そのカードが finalize されたかを見る。Counter されたカードも数える（420.4.b）。
- "use" と "play" は同じ意味。カード文面は "play" を使う（377.2）。

### 11.3 対象（355.6-355.17, 750-758）

- **Choose** で指すものは対象になる。**Pick** で指すものは対象にならない（Radiance で導入）。
- 対象として有効な条件（355.9）:
  - Board 上の Permanent か Rune、Chain 上の Finalized な Spell や能力、プレイヤー、ゾーン、または他のゾーンにあると明示されたゲームオブジェクト（例: Trash の Unit カード）、のいずれかである
  - 対象の制限を満たす
  - その Spell や能力そのものではない
  - Pending の項目は対象にできない
- 対象にならないもの（355.10）:
  - Public でないゾーンにあるもの
  - 制限としてだけ現れるもの
  - コスト・誘発条件・置換の中にだけあるもの
  - 特性で自動的に決まるもの（"all units"）
  - 他のプレイヤーが選ぶもの
  - "must" で指示されるもの
  - 自分の Legend
- "any number" や "up to" は 0 個でもよい（355.13）。ダメージの分割は 355.14。
- 決定的に不正になる選択はできない（355.16）。必須の要求と制限は 355.17。
- **Untargetability**（756-758）、**Making New Choices**（750-755）。

### 11.4 対象が不正になった場合（359.3.e）

- Spell は、対象が一部または全部不正になっても解決する。
- 不正な対象には何もしない（359.3.e.5）。
- **Ignored と Negated を区別する**（359.3.e.6）:
  - Ignored: 不正な対象や、参照情報が得られないために実行できない指示。
  - Negated: それ以外の理由（置換・スキップ・不可能など）で実行できない指示。
- **連結した指示**（359.3.e.14）:
  - 先の指示が実行されたか Negated なら、後の指示を実行する。
  - **ただし**、後の指示が先のゲームアクションの実行を直接参照する場合（"If you do" など）は、先の指示が Negated なら後の指示は実行されない（359.3.e.14.b）。
  - 先の指示が Ignored なら、後の指示も Ignored。
- 参照する情報の時点（359.3.f）:
  - "here"、"my"、"its" は実行時に評価する。
  - 誘発条件から取る情報は、誘発した時点で確定する。
  - 遅延能力は生成時点の情報を使う。

## 12. 能力（360-407）

| 種類 | 規則 | 要点 |
|---|---|---|
| Passive | 363-366 | 事実を述べる文。"if" や "while" で条件がつく。通常は Board 上でだけ有効。コストを変える Passive は、プレイできるどのゾーンでも有効（366.2） |
| Replacement | 367-375 | "as"、"would"、"instead" で表す。イベントが起きる前に適用する。**1 つのイベントに同じ置換は 1 回だけ**（370.2）。順序は影響を受けるものの Controller が決める（372） |
| Activated | 376-381 | 「コスト: 効果」の形。プレイと同じ 6 つの段を踏む（399-407） |
| Triggered | 382-385 | "when"、"at"、"the Nth time" で表す。**同時に誘発したものは、プレイヤーごとに順序を選び、Turn Player から手番順に Chain に積む**（383.3.d）。ただし戦闘開始時（Attacker / Defender の決定で誘発したもの）は、Attacker、Defender 以外の全員（手番順）、Defender の順に積む（466.2.d.1）。先頭の "you may" は finalize 時に決める（383.3.a）。Conquer での 1 点の獲得が Negate・置換されても、Conquer 効果は誘発する（383.4.c.2.c。Hold も同様: 383.4.d.2.c） |
| Reflexive | 387-389 | "Do this:" の形。解決中に新しい Pending を生む |
| Delayed | 390-393 | 遅延した誘発・置換・Passive。発生源が Board を離れても有効 |
| Linked | 394-398 | 同じオブジェクトの能力どうしが参照し合う |

- **Dependent Keyword**（727）: Legion、Level、Empowered。条件が成り立つ間だけ、後に続く文が有効になる。
- **Inactive**（720-725）: Inactive な文は誘発も適用も起動もしないが、存在はしていて参照できる。Attach されたカードでは、Rules Text が Inactive になり Effect Text が有効になる。
- **回数制限**: "once each turn" など（371, 386）。

## 13. ゲームアクション（408-446）

Draw 414、Exhaust 415、Ready 416、Recycle 417、Deal 418（有効なダメージは 1 以上の整数）、Heal 419、Play 420、Move 421、Hide 422、Discard 423、Stun 424（戦闘ダメージに Might を加えない。ターン終了時に外れる）、Reveal 425、Counter 426、Buff 427（+1 Might のカウンター。1 体に 1 個まで: 701-705）、Banish 428、Kill 429、Add 430、Channel 431、Burn Out 432、Double 433、Swap 434、Attach 435、Detach 436、Predict 437、Prevent 438、Replace 439、Create 440、Burn 441、Empower 442、Disempower 443、Skip 444、Pay 445、Copy 446。

効果 IR のプリミティブは、この一覧に対応させる（design.md §7.2）。

## 14. 移動と Recall（144, 447-460）

- **Standard Move**（144）:
  - Unit を Exhaust して移動する。
  - 自分の Main Phase で、Open かつ Showdown / Combat が無いときだけ行える。
  - **複数の Unit を同時に動かせる**（行き先は同じ、元は違ってよい）。これは 1 つのアクションとして扱う（144.3）。
  - 行き先は、Base から Battlefield、Battlefield から自分の Base。Battlefield から Battlefield へは Ganking が必要（810）。
- **Move**（447-455）:
  - 即座に完了し、途中の状態は無い。Chain を使わず、応答できない。完了後に Cleanup を行う。
  - 行き先に居られない場合は、代わりに Recall になる（449.2.c）。
  - 多人数戦では行き先が制限される: 既に他の 2 人の Unit がいる Battlefield（144.4.a.1, 451.2）、Staged か進行中の Combat がある Battlefield（449.2.a, 464）、味方が占有している Battlefield（449.2.b）は不可。
- **Recall**（456-460）: Controller の Base に戻すこと。Move ではないので、移動の誘発も移動の禁止も働かない。ダメージやステータスは変わらない。
- **Control の喪失**: Open で Showdown も Combat も無く、自分の Unit がいなくなったら、次の Cleanup で失う（323.5）。

## 15. 戦闘（461-468）

- **成立条件**: ちょうど 2 人のプレイヤーの Unit の間でだけ起きる（464）。Cleanup の時点で Chain が無く、Combat が Staged で、他に進行中の Showdown / Combat が無いときに始まる（462）。
- **手順**:

| ステップ | 規則 | 内容 |
|---|---|---|
| 1. Combat Showdown | 466 | 戦闘開始時の効果が起きる。**Attacker は Contested を付けたプレイヤー**で、もう一方が Defender。指定で誘発した能力を、Attacker → Defender 以外の全員（手番順）→ Defender の順に Chain に積む（466.2.d.1）。以降は通常の Showdown |
| 2. Combat Damage | 467 | 両陣営に Unit が残っていれば行う。各陣営の Might を合計する（Stun は加えず、負は 0）。**Attacker から順に、合計分のダメージを相手の Unit に割り当てる**。割り当て終わったら同時に与える |
| 3. Resolution | 468 | Combat Cleanup を行う: 3c で全 Unit を Heal、3d で Defender が残っていれば Attacker を Recall。続いて結果を判定し、Control を確立する（Conquer は防御側でも起こりうる: 468.5.e）。最後に指定を外し、「この戦闘」効果を失効させる |

- **割り当ての規則**（467.2.c）:
  - 割り当ては「与える（Deal）」ではない。すべて割り当て終えてから、同時に与える（467.2.c.1）。
  - ある Unit に致死量を割り当て終えるまで、次の Unit に割り当てない（467.2.c.3）。
  - 致死に必要な最小量を超えて割り当てない。他に割り当て先が無い場合を除く（467.2.c.4）。
  - すでに負っているダメージも、致死量の計算に含める。
  - ダメージの増加や置換は、割り当ての時点で考慮する（467.2.c.4.a）。
  - 割り当ての要求と制限には、できる限り従う（467.2.c.6）。
  - 同じ優先度の要求を持つ Unit が複数あれば、その中の順序は任意（467.2.c.7）。
  - 互いに排他的な要求（Tank と Backline の両方など）は、どちらか一方を選んで適用する（467.2.c.8-9）。
  - ダメージを受けられない Unit は、割り当ての義務の対象外（467.2.c.10）。
  - Prevent の値は致死量に加わる。すべてを防ぐ Prevent なら、致死にならない（438.5）。
- **キーワード**:
  - **Tank**（815）: 同じ Controller の Tank でない Unit より先に致死量を割り当てる。
  - **Backline**（826）: 同じ Controller の Backline でない Unit より後に割り当てる。
  - **Assault X**（807）: Attacker である間 +X。
  - **Shield X**（814）: Defender である間 +X。
  - **Disarm X**（831）: 攻撃時に、敵 Unit 1 体をそのターン −X。
- **Attack / Defend の誘発**: 戦闘ごとに、最初に指定を得たとき 1 回だけ（383.4.e-f）。
- **結果が出なかった場合**: 両者に Unit が残るなら、Showdown と Combat をもう一度 Staged にする（468.3.d.1）。

## 16. 得点と勝利（193-196, 469-474, 432, 649-652）

- **Scoring と Gaining Points は別物**（470）。
- **Score する方法**（471）:
  - **Conquer**: 今ターン Score していない Battlefield の Control を得る。
  - **Hold**: 自分の Scoring Step に、今ターン Score していない Battlefield の Control を保っている。
- **1 人のプレイヤーは、1 つの Battlefield を 1 ターンに 1 回だけ Score できる**（472）。制限はプレイヤー単位で、2v2 ではチーム単位（491.8.b）。
  - したがって、同じ Battlefield が 1 ターンに別々のプレイヤーに Score されることはありうる（例: 防御側の Conquer: 468.5.e）。
- Score すると最大 1 点を得て、その Battlefield の Conquer / Hold 能力が誘発する（473）。
- **Final Point**（473.1.b）: Conquer で点を得るとき、得点が Victory Score の 1 点手前以上なら、次のようになる。
  - 今ターンにすべての Battlefield を Score していれば、最後の 1 点を得る。
  - そうでなければ、点の代わりに 1 枚引く。
  - この制限は Conquer にだけかかる（473.1.a.1）。
- **勝利**: Cleanup の手順 1（323.1, 474）で判定する。効果による勝利、最後の 1 人になった場合もある（195）。
  - Victory Score の既定は 8（194.3）。モデルでは、パッシブ能力の増減を含めて、`GameState.victoryScore` が読む。
  - 同点なら続行する（194.2.b）。**Core Rules に引き分けの規定は無い。** 大会のルールでは、ループ（TR 505.6）、時間切れ（TR 408.2.b）、合意（TR 410.1）で引き分けになる（[tournament-model.md](tournament-model.md)）。
- **得点は 0 未満にならない**。0 点のときに点を失っても何も起きず、それに誘発する効果も起きない（194.4）。→ 得点は単調増加ではない。
- **Burn Out**（432）:
  - 置換効果である（432.5）。Main Deck の残りより多く引いたり移したりしようとすると起きる。
  - 手順: できるだけ実行する → Trash を Main Deck に Recycle する（ランダム）→ 対戦相手 1 人を選び、その人が 1 点を得る → 残りを実行する。
  - Main Deck も Trash も空なら繰り返す。
  - 2 回目以降の Burn Out で得る点は、置換も防止もできない（432.3.b）。
  - 2 回目以降の点で勝利条件を満たしたら、Cleanup を待たずに即座に勝つ（432.3.c.1）。
  - look や reveal では起きない（432.1.c）。
- **投了**（649-652）:
  - いつでもできる（650）。
  - 投了後に残りが 1 人なら、その人が勝つ（651.1）。
  - 投了後に 2 人以上が残る場合は、除去の手順（652）を行う: 所有物の Banish、Battlefield のトークンへの置き換え、Spell の Counter など（651.2）。
  - 味方がいるモードでは、投了したプレイヤーの味方も敗北し、除去される（651.4）。

## 17. Layers（475-482）

- 適用順（479）:
  1. **Copy**: Radiance で新設された最初の層。
  2. **Trait-Altering**: 名前、Supertype、型、Tag、**Controller**、コスト、ドメイン、基本 Might。
  3. **Ability-Altering**: キーワード、Passive、文の追加と削除、Attach されたカードの Effect Text。
  4. **Arithmetic**: Might、コスト。**増加を先に、減少を後に適用する**（479.4.e）。Passive でない効果の制限（最低 1 など）は、適用時点で固定される（479.4.b）。
- オブジェクトごとに評価する。他のオブジェクトの情報に依存する効果は、参照先を先に評価する。依存がループする場合は、最小の集合を同時に評価する（478.1）。
- **1 巡で終わりではない。** 層を順に適用し終えたら、もう一度すべての層を評価し、新たに適用可能になった効果を適用する。変化がなくなるまで繰り返す。ただし各効果の適用は 1 回だけで、効果の除去も 1 回だけ（478.2-478.4）。
  - 例: Arithmetic 層で Might が上がって Mighty になると、Ability-Altering 層の「Mighty である間〜を持つ」が新たに適用される。
- **同一層内の依存関係**（480-481）: 一方の適用が、他方の存在・対象の数・結果を変えるなら依存している。変えられる側を後に適用する。互いに変えあう場合は依存なしとする。
- 依存が無ければ **timestamp 順**（482）。Inactive になると timestamp を失い、戻ったときに新しい timestamp を得る。

## 18. ゲームモード（483-491）

| モード | 規則 | 人数 | Victory Score | Battlefield の数 | 最初のターンの調整 |
|---|---|---|---|---|---|
| 1v1 Duel | 487 | 2 | 8 | 2（各自 3 枚から 1 枚をランダムに選ぶ） | 後手は最初の Channel で 1 枚多く Channel する |
| 1v1 Match | 488 | 2 | 8 | 2（各自が選ぶ。Best of 3） | Duel と同じ |
| FFA3 Skirmish | 489 | 3 | 8 | 3 | 先手は最初の Draw で引かない。最後の手番の人は 1 枚多く Channel する |
| FFA4 War | 490 | 4 | 8 | 3 | FFA3 と同じ |
| 2v2 Magma Chamber | 491 | 4 | **11** | 3 | FFA3 と同じ。手番はチームが交互になる |

2v2 の固有規則（491.8）:
- 得点はチームで共有する。
- Battlefield はチームごとに 1 ターン 1 回だけ Score できる。
- Control は共有しない。
- 味方のターンに行動できるのは、招待されたときだけ。
- Final Point の条件が調整される。

## 19. キーワード（805-832、28 個）

| 規則 | キーワード | 種類 | 要点 | 導入 |
|---|---|---|---|---|
| 805 | Accelerate | 任意の追加コスト | Energy 1 と自分のドメインの Power 1 を追加で払うと、ready で入る（置換） | Origins |
| 806 | Action | 許可 | Showdown 中（相手のターンでも）プレイ・起動できる | Origins |
| 807 | Assault X | Passive | Attacker である間 +X。複数あれば合算 | Origins |
| 808 | Deathknell | 誘発 | 死んだときの効果。Trash へ移る前に Pending として加える | Origins |
| 809 | Deflect X | Passive | 相手がこれを対象にするとき、追加コストとして任意ドメインの Power を X 払う | Origins |
| 810 | Ganking | Passive | Standard Move で Battlefield から Battlefield へ移動できる | Origins |
| 811 | Hidden | 許可 | `[A]` を払って伏せて置き（Hide）、次のターン以降に Reaction を得て、基本コストを無視してプレイできる | Origins |
| 812 | Legion | Dependent | 今ターンに他のカードを finalize していれば有効 | Origins |
| 813 | Reaction | 許可 | Action の許可に加え、Closed 中にもプレイ・起動できる | Origins |
| 814 | Shield X | Passive | Defender である間 +X | Origins |
| 815 | Tank | Passive | 致死ダメージを先に割り当てられる | Origins |
| 816 | Temporary | 誘発 | Controller の Beginning Phase の開始時（Scoring より前）に kill される | Origins |
| 817 | Vision | 誘発 | プレイされたとき Predict する | Origins |
| 818 | Equip [Cost] | 起動 | 自分の Unit に Attach する | Spiritforged |
| 819 | Quick-Draw | 誘発・許可 | Reaction を持ち、プレイ時に Attach する | Spiritforged |
| 820 | Repeat [Cost] | 任意の追加コスト | 払うと、効果をもう一度実行する | Spiritforged |
| 821 | Weaponmaster | 誘発 | プレイ時に Equipment を割引して Attach できる | Spiritforged |
| 822 | Ambush | Passive | 自分の Unit がいる Battlefield に、Reaction としてプレイできる | Unleashed |
| 823 | Hunt X | 誘発 | Conquer または Hold したとき XP を X 得る | Unleashed |
| 824 | Level N | Dependent | XP が N 以上の間、有効 | Unleashed |
| 825 | Unique | 構築制限 | 同名は 1 枚まで | Unleashed |
| 826 | Backline | Passive | 致死ダメージを後に割り当てられる | Unleashed |
| 827 | Empower [Cost] | 起動 | 自分を Empowered にする | Vendetta |
| 828 | Empowered | Dependent | Empowered である間、有効 | Vendetta |
| 829 | Flow [Cost] | Passive | Trash から Flow のコストでプレイでき、その後 Banish される | Vendetta |
| 830 | Deploy | Passive・誘発 | どの Battlefield にも出せる。相手がそこを Hold したら kill される | Radiance |
| 831 | Disarm X | 誘発 | 攻撃時に、敵 Unit 1 体をそのターン −X | Radiance |
| 832 | Show Off [Object] | Passive | プレイ時に、条件を満たすカードを見せるか選ぶ | Radiance |

「導入」の列は、パッチノートと各セットの記述からの推定を含む。Unique は Spiritforged のカードに初出という調査結果もあり、正確な時期は未確認。

## 20. モデル化上の決定（まとめ）

| 論点 | 決定 | 根拠 |
|---|---|---|
| Open / Closed | 保存せず、Chain の有無から導出する | 309 |
| オブジェクトの同一性 | Non-Board ゾーンを出入りするたびに新しい ObjId を払い出す。古い ObjId の情報は消えるので、誘発した時点の情報は値として写しておく | 124, 359.3.f |
| 継続効果 | Passive は保存せず、盤面から導出する。期間つき効果は「効果 + timestamp + 期間」のリストとして保存する。実効特性はどちらからも Layers で毎回導出する。反復は、効果の数で決まる上限の中で必ず止まる | 475-482 |
| Controller | 表には基底の値を保存する。規則の判定には、Layers で導出した実効の値を使う | 479.2, 188-192 |
| 導出値への誘発 | 「Mighty になったとき」などは、処理の 1 歩の前後で実効特性を比べて検出する | 709 |
| プレイ時の選択 | 対象とモードは、効果の本体から分けて宣言する。プレイの時点で必要な選択が、効果を実行せずに分かる | 355 |
| 置換と防止 | 盤面の変更はすべて「提案 → 置換・防止 → 適用 → 発行」の経路を通す。Burn Out もこの経路の置換として扱う | 367-375, 438, 432.5 |
| Score の記録 | 今ターンに Score した（プレイヤー、Battlefield）の組を持つ | 472 |
| 巻き戻し | プレイ手順の開始時の盤面を保存し、合法性の確認に失敗したら戻す。支払い中に起動した Add 能力の結果も戻す（§21 の 13） | 358.5 |
| 状態ベースの処理 | Cleanup に集約し、変化が止まるまで繰り返す（fuel つき）。不動点で成り立つ条件は、構造の不変条件（`WF`）とは別の述語（`Settled`）にする | 318-324 |
| 同時イベント | 1 つのアクションが生むイベントは 1 ステップで同時に扱う。誘発の順序はプレイヤーの選択と手番順で決める | 303, 370.1.a.2, 383.3.d |
| 組合せになる決定 | 戦闘ダメージの割り当てや誘発の順序は、「次の 1 つを選ぶ」決定の列に分ける。列の途中では盤面を変えず、終わった時点で 1 つのアクションとして実行する | 467.2.c, 144.3, 383.3.d, 417.5.a, 355.13 |
| 乱数 | 偶然の決定として外から受け取る | 114, 115, 417.5, 432.2.b, 487.5 |
| 支払い | Rune の Add 能力と Rune Pool を忠実に表し、支払い方をプレイヤーが選ぶ | 164, 357, 430, 445 |
| 勝利 | Cleanup の手順 1 で判定する。Burn Out の連続による即時勝利は例外として扱う | 323.1, 432.3.c.1 |
| ループ | CR に無限ループの規定は無い。自動処理は fuel つきで回し、尽きたらエラーにする。大会のルールでの引き分けは、ジャッジを行為者とする決定として外から受け取る。エンジンは自動では検出しない（[tournament-model.md §5](tournament-model.md#5-ループtr-505)） | TR 505.6 |
| 初期の対象モード | 1v1 Duel から。型は N 人で作る | 487 |
| ゲームの外のカード | 構築時に追加で選んだ Legend や、除去の手順で置き換えられた Battlefield は、エンジン内部用のゾーン（`outOfGame`）に置く | 103.1, 652 |

## 21. 曖昧な点と要確認事項

1. **PDF 内の古い相互参照**:
   - 161.2.a は Rune Deck を「103.3」と書いているが、実際は 103.4。
   - 133.7.a / 133.7.b も 1 つずれている。
   - 377.3.b.1 は「rule 398」を指すが、本体は 399。
2. **Cleanup の手順ラベルの欠番**: 3a の次が 3c、3d、3e（特殊 Cleanup が挿入するもの）で、3b は無い。順序は保たれていると読める。
3. **フェイズ名の揺れ**: "Awaken Phase" と "Awakening Phase"。424.1.a.2 は旧称 "end of turn cleanup" を使っている。
4. **Combat Cleanup の Heal**（468.1.a.1）: 文言上は戦闘した Battlefield に限らず、全 Unit が対象。文字どおりに実装し、FAQ で確認する。
5. **Final Point で点の代わりに引いた場合**も、Conquer の能力は誘発する。これは 383.4.c.2.c に明記されている（「Conquer での 1 点の獲得が Negate・置換されても誘発する」）。曖昧点ではないが、見落としやすいので残しておく。
6. **2v2 の Final Point**: 491.8.g.1 は「味方が occupied」、315.2.b.3 と 491.8.b.1 は「味方が control」と、用語が揺れている。
7. **同時に誘発したもの**: Chain に積む順序（383.3.d）と、後入れ先出しの解決（340.1）を組み合わせると、解決順は逆になる。これは推論であり、明文ではない。
8. **Rune Deck**: 同名の枚数制限、ドメインごとの内訳、Basic 以外の Rune の定義が Core Rules に無い。
9. **Main Deck の枚数**: Core Rules（40 枚以上）と Tournament Rules の Constructed（ちょうど 40 枚）の差。大会では TR が優先する（TR 104.1）ので、フォーマットごとの述語で扱う。
10. **Public ゾーンの一覧の不一致**: 355.10.a.1 の一覧は Chain と Banishment を含まない。一方、108.1.b と 108.6.e はそれらを Public としている。対象としての Public と、情報としての Public が別物かどうかは不明。
11. **ループ**: Core Rules には無限ループの扱いの規定が無い。Cleanup の反復、Expiration のループ、Burn Out の繰り返し、No Result の後の再戦闘で、止まらない可能性がある。Tournament Rules は、誰も維持していない止まらないループを引き分けとする（TR 505.6）。モデルでの扱いは [tournament-model.md §5](tournament-model.md#5-ループtr-505)。
12. **Layers の依存判定**（480）は、「適用順を入れ替えると結果が変わるか」を判定する必要があり、決定的に実装するには試行計算が要る。
13. **巻き戻しの範囲**（358.5）: CR は「undone」と書くだけである。支払い中に起動した Add 能力の結果（Rune の Exhaust、Rune Pool）まで戻るかは明記されていない。806.4.b は、カードを元のゾーンに戻すとも書いている。モデルでは「プレイ手順の開始時の盤面にすべて戻す」と決め、FAQ で確認する。
14. **戦闘の手順の記述の関係**: 467.3 は「FEPR を飛ばして Resolution Step へ進む」とし、468.2 にも注記がある。両者の関係は、戦闘を実装するときに原文で確かめる。

## 22. 版ごとの主な変更（モデルへの影響）

| 版 | 時期 | 主な変更 |
|---|---|---|
| 初回のパッチ | 2025-10 | "Can't beats can" と "Do as much as you can"、Domain Identity を Legend に紐づける、Pending / Finalize と FEPR、Cleanup の繰り返し、Contested、Delayed 能力 |
| Spiritforged | 2025-12 | Attach / Equipment / Equip / Quick-Draw / Weaponmaster / Repeat、Inactive な文、Chain 上の能力が Controller を保持する |
| Unleashed | 2026-03 | XP / Hunt / Level、Ambush / Unique / Backline、勝利判定を Cleanup に統一、Showdown / Combat の Staged 化、HOT FEPR、フェイズ名の変更（Action → Main、End of Turn → Ending）、Replace / Create / Predict / Prevent、追加ターン |
| Vendetta | 2026-07 | Empower / Flow / Burn / Skip、トークンが Supertype でなくなる、Energy と Power の支払いが任意になる、"play" の語義の整理 |
| Radiance | 2026-10 | Deploy / Disarm / Show Off、Copy 層の新設（4 層構成）、Unit は Attach されない、Pick と Choose の区別、Ignored と Negated の区別、Pending は対象にできない |
| Legacy（予告） | 2027-01 | 書式の全面刷新（規則番号の変更）、カード文面のテンプレート変更 |
