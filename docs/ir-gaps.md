# 効果 IR の不足の一覧

カードの効果を IR の値として転記して、書けた文と書けなかった文を分けた記録（[roadmap.md](roadmap.md) M3b）。転記のたびに更新する。

## 1. 転記の範囲と結果（2026-11-21、1 回目）

対象は、Proving Grounds の 24 枚と、[card-data.md §7](card-data.md#7-モデルにとって難しいカード先に設計で考慮しておくもの) の難しいカードを実カードから探して見つけた 22 枚（Renekton、Blue Sentinel、Fanfare、Dune Surfer など、新しいセットの例を含む）。

| 結果 | 枚数 | カード |
|---|---|---|
| IR で書けた（`drafted`） | 39 | OGS の 23 枚、Time Warp、Rhasa、Possession、Karthus, Eternal、Aspirant's Climb、The Grand Plaza、Forgotten Monument、Smite、Blue Sentinel、Dune Surfer、Renekton（Rage Fueled と Brute）、Otterpus、Ki Barrier、Fanfare、Seraphic Wyvern |
| 書けなかった | 7 | Recruit the Vanguard（OGS-015）、Mystic Reversal、Heimerdinger, Inventor、Svellsongur、Mirror Image、Whirlwind、Heimerdinger, Academy Instructor |

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
| Mystic Reversal | "Gain control of a spell. You may make new choices for it." | 解決前の Spell への参照、選び直し（CR 750-755） |
| Heimerdinger, Inventor | "I have all Exhaust abilities of all friendly legends, units, and gear." | 他のオブジェクトの能力を得ること |
| Svellsongur | "copy that unit's text to this Equipment's effect text for as long as this is attached to it" | 文のコピー（CR 479.1）、Attach に連動する期間 |
| Whirlwind | "Starting with the next player, each player may return a unit ..." | 手番順に従ってプレイヤーを走査する（多人数。M9） |
| Heimerdinger, Academy Instructor | "If you would play a unit token to a location ... play a 3 Might Mech unit token to that same location instead." | トークンのプレイを置換すること、置換前の場所を参照すること |

## 4. 書けたが、近似したもの

| カード | 近似 |
|---|---|
| Firestorm | 「a battlefield」を、プレイ時に Battlefield を 1 つ選ぶ、と読んだ（原文は選ぶと書いていない） |
| Karthus, Eternal | Deathknell を「死んだときの誘発すべて」で表した。キーワードの Deathknell だけに絞る手段が無い |
| Smite | "If it would die this turn" を「次に死ぬとき」で表した。ユニットは 1 回しか死なないので同じ |
| Blue Sentinel | "at the start of your next Main Phase" を、自分の次の Main Phase 開始の遅延効果で表した。`delayed` の期間は `permanent`（発火するまで） |
| Forgotten Monument | 「その場所で、プレイヤーが自分の 3 ターン目まで得点できない」を `untilTurn := 3` で表した |
| Lux, Illuminated ほか | 「コストが 5 以上の Spell をプレイしたとき」を、トリガーの subject に Spell のフィルタを置いて表した。subject は「イベントの対象」と「世界にあるもの」の両方を表せてしまい、解釈器で意味を決める必要がある |

## 5. 次にすること

- 静的な検査（`CardDB.WF`）: 変数の束縛、`Selector.slot` の番号が `EffectDef.choices` の対象枠の範囲内であること。転記したカードが満たすことを確かめる。
- 出現の多いテンプレートの上位 100 種を転記して、不足の洗い出しを続ける。
- 書けなかった文のうち、トークンの定義とコピーは、M4 の設計（トークンと Copy 層）に合わせて足す。
