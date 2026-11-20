# docs

| 文書 | 内容 | 編集者 |
|---|---|---|
| [original.md](original.md) | **要求の正本。** 他の文書と食い違う場合はこれを優先する | 人間のみ |
| [design.md](design.md) | 実装方針（要求の整理、前提とする版、設計原則、全体構成、データモデル、エンジンと `Legal` 仕様、効果 IR、証明の方針、版管理、カードデータと権利、テストと CI、未決事項、リスク） | エージェント・人間 |
| [roadmap.md](roadmap.md) | マイルストーン M0〜M10（M10 は完了判定）と、証明を積み上げる順序、不変条件のカタログ、カードの実装状況の定義 | エージェント・人間 |
| [rules-model.md](rules-model.md) | Riftbound Core Rules（2026-10-09 版）を形式化の観点で整理したもの。規則番号つき | エージェント・人間 |
| [lean-guidelines.md](lean-guidelines.md) | Lean 4 のコーディング規約（ツールチェーン、Lake、module system、命名、証明しやすい書き方、テスト、CI） | エージェント・人間 |
| [card-data.md](card-data.md) | カードデータの取り込み、効果 IR への写像、新カードと新キーワードの追加手順、権利面の注意 | エージェント・人間 |

読む順番: `original.md` → `rules-model.md`（ルール用語を押さえる。§7〜§11 だけでもよい）→ `design.md` → `roadmap.md`。`lean-guidelines.md` と `card-data.md` は、作業に応じて参照する。

文書の前提（2026-11-20 時点）:
- ルール: Riftbound Core Rules, Last Updated 2026-10-09
- カードプール: Origins〜Radiance
- Lean: v4.36.0
