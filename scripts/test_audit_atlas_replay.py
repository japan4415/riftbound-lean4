import unittest

from audit_atlas_replay import audit


class AtlasReplayAuditTest(unittest.TestCase):
    def test_opening_counts_shared_and_masked_entries_without_emitting_private_data(self):
        replay = {
            "format": "riftatlas-replay",
            "version": 2,
            "nodes": [
                ["o", [["frames", {"r": 1}], ["unusedCycle", {"r": 0}]]],
                ["a", [None, {"state": {"r": 2}}, {"state": {"r": 3}}]],
                ["o", [["phase", "mulligan"], ["players", {"r": 4}]]],
                ["o", [["phase", "in_game"], ["players", {"r": 4}]]],
                ["a", [
                    {"seat": 1, "name": "hidden name", "board": {
                        "hand": ["__hidden_zone__"], "deck": [], "runeDeck": None,
                    }},
                    {"seat": 0, "name": "visible name", "registeredDeck": {"raw": "private deck text"},
                     "board": {"hand": {"r": 5}, "deck": {"r": 6}, "runeDeck": []}},
                ]],
                ["a", [{"r": 7}]],
                ["a", [{"r": 7}, {"id": "__hidden_zone__", "cardCode": "__hidden_zone__"}]],
                ["o", [["id", "unprinted id"], ["cardCode", "TEST-101"]]],
            ],
            "root": {"r": 0},
        }
        self.assertEqual(audit(replay), {
            "sourceVersion": 2,
            "sourceFrames": 3,
            "sourceFramesWithState": 2,
            "firstMulliganFrame": 1,
            "firstInGameFrame": 2,
            "hasFinalOutcome": False,
            "seats": [
                {"seat": 0, "hasDeckListText": True, "mulliganZones": {
                    "hand": {"entries": 1, "withCardCode": 1},
                    "mainDeck": {"entries": 2, "withCardCode": 1},
                    "runeDeck": {"entries": 0, "withCardCode": 0},
                }},
                {"seat": 1, "hasDeckListText": False, "mulliganZones": {
                    "hand": {"entries": 1, "withCardCode": 0},
                    "mainDeck": {"entries": 0, "withCardCode": 0},
                    "runeDeck": None,
                }},
            ],
        })

    def test_capture_that_starts_in_play_leaves_the_opening_unknown(self):
        result = audit({
            "format": "riftatlas-replay",
            "nodes": [["o", [["frames", [
                {"state": {"phase": "in_game", "players": [{"seat": 0}]}},
                {"state": {"phase": "mulligan", "players": [
                    {"seat": 0, "decklistRaw": "imported list", "board": {"hand": []}},
                ], "gameOutcome": {"winnerPlayerIds": ["private id"]}}},
            ]]]]],
            "root": {"r": 0},
        })
        self.assertIsNone(result["firstMulliganFrame"])
        self.assertEqual(result["firstInGameFrame"], 0)
        self.assertTrue(result["hasFinalOutcome"])
        self.assertEqual(result["seats"], [
            {"seat": 0, "hasDeckListText": True,
             "mulliganZones": {"hand": None, "mainDeck": None, "runeDeck": None}},
        ])

    def test_same_format_tag_does_not_confuse_patch_exports_with_native_frames(self):
        with self.assertRaisesRegex(ValueError, "expected the History & Replays JSON"):
            audit({"format": "riftatlas-replay", "version": 1, "commits": [], "origin": {}})

    def test_invalid_references_do_not_alias_valid_nodes(self):
        for invalid in (-1, 1, False, "0"):
            with self.subTest(invalid=invalid):
                with self.assertRaisesRegex(ValueError, "invalid replay node reference"):
                    audit({"format": "riftatlas-replay", "nodes": [["o", []]], "root": {"r": invalid}})

    def test_no_state_is_an_error(self):
        replay = {
            "format": "riftatlas-replay",
            "nodes": [["o", [["frames", [None]]]]],
            "root": {"r": 0},
        }
        with self.assertRaisesRegex(ValueError, "no source frames with state"):
            audit(replay)


if __name__ == "__main__":
    unittest.main()
