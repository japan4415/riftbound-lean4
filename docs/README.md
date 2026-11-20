# docs

| 文書 | 内容 | 編集者 |
|---|---|---|
| [original.md](original.md) | **要求の正本。** 他の文書と食い違う場合はこれを優先する | 人間のみ |
| [design.md](design.md) | 実装方針（要求の整理、前提とする版、設計原則、全体構成、データモデル、エンジンと `Legal` 仕様、イベントの経路、効果 IR、証明の方針、版管理、カードデータと権利、テストと検証、決定事項、リスク） | エージェント・人間 |
| [roadmap.md](roadmap.md) | マイルストーン M0〜M10（途中に M3b と M5b。M10 は完了判定）と、証明を積み上げる順序、不変条件のカタログ（I1〜I19）、カードの実装状況の定義 | エージェント・人間 |
| [rules-model.md](rules-model.md) | Riftbound Core Rules（2026-10-09 版）を形式化の観点で整理したもの。規則番号つき | エージェント・人間 |
| [tournament-model.md](tournament-model.md) | Riftbound Tournament Rules（2026-10-09 版）のうち形式化の対象にする部分（フォーマット、マッチ、時間切れ、ループ） | エージェント・人間 |
| [lean-guidelines.md](lean-guidelines.md) | Lean 4 のコーディング規約（ツールチェーン、Lake、module system、命名、証明しやすい書き方、テスト、作業の単位とローカルでの検証） | エージェント・人間 |
| [card-data.md](card-data.md) | カードデータの取り込み、効果 IR への写像、新カードと新キーワードの追加手順、権利面の注意 | エージェント・人間 |
| [ir-gaps.md](ir-gaps.md) | 効果 IR に転記して分かった不足の一覧（IR を直したもの、書けなかった文、近似したもの） | エージェント・人間 |
| [viewer.md](viewer.md) | エンジンが動かした 1 ゲームをアニメーションで再生するビューア（トレースの書き出しと再生。何が保証されて、何がされないか） | エージェント・人間 |

読む順番: `original.md` → `rules-model.md`（ルール用語を押さえる。§7〜§11 だけでもよい）→ `design.md` → `roadmap.md`。`lean-guidelines.md` と `card-data.md` は、作業に応じて参照する。

文書の前提（2026-11-20 時点）:
- ルール: Riftbound Core Rules, Last Updated 2026-10-09 と、Riftbound Tournament Rules, Last Updated October 9, 2026
- カードプール: Origins〜Radiance
- Lean: v4.36.0
