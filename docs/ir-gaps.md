# 効果 IR の不足の一覧

カードの効果を IR の値として転記して、書けた文と書けなかった文を分けた記録（[roadmap.md](roadmap.md) M3b）。転記のたびに更新する。

## 1. 転記の範囲と結果（2026-11-21、1 回目）

対象は、Proving Grounds の 24 枚と、[card-data.md §7](card-data.md#7-モデルにとって難しいカード先に設計で考慮しておくもの) の難しいカードを実カードから探して見つけた 22 枚（Renekton、Blue Sentinel、Fanfare、Dune Surfer など、新しいセットの例を含む）。

| 結果 | 枚数 | カード |
|---|---|---|
| IR で書けた（`drafted`） | 39 | OGS の 23 枚、Time Warp、Rhasa、Possession、Karthus, Eternal、Aspirant's Climb、The Grand Plaza、Forgotten Monument、Smite、Blue Sentinel、Dune Surfer、Renekton（Rage Fueled と Brute）、Otterpus、Ki Barrier、Fanfare、Seraphic Wyvern |
| 書けなかった | 6 | Recruit the Vanguard（OGS-015）、Mystic Reversal、Heimerdinger, Inventor、Svellsongur、Mirror Image、Heimerdinger, Academy Instructor |

キーワードだけのカード（Zephyr Sage、Garen, Rugged）は、キーワードが生成ブロックにあるので、`drafted` にした。

## 2. 転記で見つかり、IR を直したもの

| 文 | 足りなかったもの | 直し方 |
|---|---|---|
| "Deal 3 to all enemy units at a battlefield"（Firestorm） | 選んだ Battlefield にいること | `Filter.at_ (s : Selector)` |
| "defends alone"（Wuju Bladesman） | 戦闘で自分の側に 1 体だけ | `Filter.alone` |
| "While you have 8+ runes, I have +4 Might"（Master Yi） | 条件つきの Passive | `Ability.passive` に `cond` を足した |
| "Move up to 2 friendly units to base" | 移動先が Base | `Dest`（`Dest.base`、`Dest.at_ s`） |
| "I enter ready"（Master Yi、Vanguard Attendant） | 場に出るときの状態 | `StaticMod.entersReady` |
| "Your spells and abilities deal 1 Bonus Damage" | ダメージの増加 | `StaticMod.bonusDamage` |
| `[Reaction]` を持つ起動型能力（Lux, Crownguard） | 能力の速さ | `Ability.activated` に `Speed` を足した |
| "[Add] 2. Use only to play spells" | 使い道が限られた資源 | `Prim.addEnergy`・`addPower` に `only : Option Act` |
| "recall it exhausted" | Exhausted で Recall | `Prim.recall` に `exhausted : Bool` |
| "The next time it dies this turn, ... instead" | 1 回だけの置換 | `Effect.replaceNext` と `ReplaceEvent` を `Effect` より前へ |
| "When you conquer / hold"（Legend、Battlefield） | プレイヤーに起きる誘発 | `TriggerEvent.youConquer`・`youHold` |
| "When my Might becomes 10 or more" | しきい値の誘発 | `TriggerEvent.mightAtLeast` |
| "the next three times you play a unit" | 回数つきの誘発 | `Occurrence`（`every`・`nth`・`next`）が `Trigger.nth` を置き換え |
| "at the start of your next Main Phase" | フェイズの開始 | `Timing.startOfMain` |
| "Your Deathknell effects trigger an additional time" | 誘発回数の hook | `StaticMod.triggersExtra` |
| "Players can't score here until their third turn" | プレイヤーへの禁止 | `StaticMod.cantPlayer`、`Amount.turnsTaken` |
| "You ignore Tank while assigning combat damage here" | 場所を限った無視 | `StaticMod.ignoreKeyword` に `where_` |
| "channel that many runes plus 1 exhausted rune instead" | 置換前の量、Exhausted の Rune | `Amount.eventAmount`、`Prim.channel` に `extraExhausted` |
| "they draw 1 instead" | 置換されるイベントのプレイヤー | `PlayerSel.eventPlayer` |
| "from conquering or holding ... 1 point" | 得点の出どころ | `Condition.scoreFrom`、`ScoreSource` |
| "Prevent the next 7 damage" | ダメージの防止 | `Effect.preventNext` |

あわせて、カードを書きやすくする補助関数（`Riftbound/Card/IR/Build.lean`）を足した。

## 3. IR で書けなかった文

| カード | 文 | 足りないもの |
|---|---|---|
| Recruit the Vanguard | "Play four 1 Might Recruit unit tokens." | トークンの定義（名前、型、Might）と、プレイする場所の選択。`Prim.create` は名前と場所だけ |
| Mirror Image | "Play a ready Reflection unit token ... It becomes a copy of that unit. Give it [Temporary]." | 作ったオブジェクトを後続の指示で参照すること、コピー（CR 479.1）、トークンの定義 |
| Heimerdinger, Inventor | "I have all Exhaust abilities of all friendly legends, units, and gear." | 他のオブジェクトの能力を得ること |
| Svellsongur | "copy that unit's text to this Equipment's effect text for as long as this is attached to it" | 文のコピー（CR 479.1）、Attach に連動する期間 |
| Whirlwind（2 人戦では書けた） | "Starting with the next player, each player may return a unit ..." | 手番順に従ってプレイヤーを走査する（多人数。M9）。2 人戦は `eachPlayer .eachOpponent` の次に `eachPlayer .you` |
| Heimerdinger, Academy Instructor | "If you would play a unit token to a location ... play a 3 Might Mech unit token to that same location instead." | トークンのプレイを置換すること、置換前の場所を参照すること |

## 4. 書けたが、近似したもの

| カード | 近似 |
|---|---|
| Firestorm | 「a battlefield」を、プレイ時に Battlefield を 1 つ選ぶ、と読んだ（原文は選ぶと書いていない） |
| Karthus, Eternal | Deathknell を「死んだときの誘発すべて」で表した。キーワードの Deathknell だけに絞る手段が無い |
| Daughter of the Void | 「呪文をプレイするときだけ使える」を、「手札に呪文があるときだけ使える」で表した（足した Power は、呪文以外のプレイにも使える） |
| Mystic Reversal | 「新しく選び直してもよい」を、書かなかった（呪文の対象は、そのまま。奪った呪文の対象は、解決のときに、再検証されないので、新しいコントローラーから見て、不正な対象（元の「味方のユニット」など）にも、効く） |
| Unlicensed Armory | The Boss と同じ（死んだ後に、墓地から戻す）。印は、ユニットの ID に付く（戻ったユニットは、新しいオブジェクトなので、もう一度は働かない）。戻す処理は、ギアの誘発なので、ギアが先に場を離れると、働かない（規則では、遅延効果なので、ギアと無関係）。捨てるのは、コストではなく、解決のとき |
| Zhonya's Hourglass | The Boss と同じ（死んだ後に、墓地から戻す）。ギアが場にあるとき、1 回だけ |
| The Boss | 「死ぬかわりに戻す」を、「死んだ後に、墓地から `playFree` で戻す」で表した（置換効果が無いため）。死んだときの誘発（Deathknell、「死んだとき」）と、「ユニットが死んだ」記録が働き、戻ることは「プレイ」として数える（Legion・「プレイしたとき」の誘発）。持ち主と操作者が違うユニットと、トークンは、救えない。準備完了で入るユニットは、準備完了で戻る |
| Smite | "If it would die this turn" を「次に死ぬとき」で表した。ユニットは 1 回しか死なないので同じ |
| Blue Sentinel | "at the start of your next Main Phase" を、自分の次の Main Phase 開始の遅延効果で表した。`delayed` の期間は `permanent`（発火するまで） |
| Forgotten Monument | 「その場所で、プレイヤーが自分の 3 ターン目まで得点できない」を `untilTurn := 3` で表した |
| Retreat（OGN-104） | 「Its owner channels」を `PlayerSel.you` で表した。友軍の Unit の owner と controller が違う場合（take control の後）は、誤る。「slot の物体の owner」を表す `PlayerSel` が無い |
| Gust（OGN-169） | 「3 Might or less」の Might フィルタは、印刷の Might、持続する増減、Buff を読む。Equipment の加算と Passive は読まない（`mightNow` は、フィルタより後で定義されている） |
| Lux, Illuminated ほか | 「コストが 5 以上の Spell をプレイしたとき」を、トリガーの subject に Spell のフィルタを置いて表した。subject は「イベントの対象」と「世界にあるもの」の両方を表せてしまい、解釈器で意味を決める必要がある |

## 5. 2 回目の転記（文の型で機械的に書いた）

`scripts/transcribe.py` が、次の型の文だけを IR の値にする。型に合わない文が 1 つでもあるカードは、書かずに残す。

| 型 | IR |
|---|---|
| `Deal N to a unit.`（`at a battlefield`・`here`・`friendly`・`enemy` つき） | 対象を宣言して `deal` |
| `Kill / Ready a unit.`、`[Stun] an enemy unit.` | 対象を宣言して `kill`・`ready`・`stun` |
| `Give a unit +N / -N :rb_might: this turn.`、`Give me +N ...` | 対象を宣言して `grant`（`mightPlus`・`mightMinus`） |
| `Draw N.`、`Discard N.` | `draw`・`discard` |
| `Return a spell from your trash to your hand.` | `returnToHand` |
| `When you play me / I attack / defend / conquer / hold, ...`、`[Deathknell] — ...`、`At the end of your turn, ...`（`you may` つき） | `Ability.triggered` |
| `I enter ready.`、`[Empowered][>] I have +N :rb_might:.` | `Ability.passive` |
| キーワードだけの行 | 何も足さない（生成ブロックの `keywords` に入っている） |

結果: 78 枚を書いた（効果ありが 22 枚、キーワードだけが 56 枚）。合計は 117 枚（1,103 枚の 10.6%）。表は [coverage.md](coverage.md)。

**長い裾野が確かめられた。** 書けなかったカードの 1,159 行は、1,105 種類の文の型に分かれ、最も多い型でも 6 回しか出ない（`S: [Reaction] — [Add] S.`）。次に多いのは 5 回（`This enters exhausted.`）、4 回（`When you play me, draw N.` の条件つき、`You may play me to an open battlefield.`）。型を 1 つ足すと 2〜6 行しか減らない。**文の型を 1 つずつ足す方式は、収穫が急に減る。** 先に進むには、解釈器と並行して、文を部品（対象の名詞句、動詞、条件、誘発）から組み立てる方式にするか、カードを 1 枚ずつ手で書くかを選ぶことになる。

また、装備品 35 枚の「付けた Unit に与える文」（`effect` 欄）を、M3b-1 の正規化が落としていた。`text` を優先して `effect` を捨てていたため。直して、`effectText` として別に持つようにした（生成ブロックにも載る）。この 35 枚は、付けた Unit に与える文を IR で表す手段がまだ無いので、転記しない。

## 6. 次にすること

- 静的な検査（`CardDB.WF`）は済んだ（[roadmap.md](roadmap.md) M3b-5）。転記したカード 39 枚は通る。
- 装備品の「付けた Unit に与える文」（`effectText`）を IR で書く手段（`Attach` に連動する能力の付与）。
- 文を部品から組み立てる方式（§5 の末尾）を決める。
- 書けなかった文のうち、トークンの定義とコピーは、M4 の設計（トークンと Copy 層）に合わせて足す。
