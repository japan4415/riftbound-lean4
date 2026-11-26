module

public import RiftboundCards.Registry
public import RiftboundCards.BanList

/-!
# RiftboundCards

Card definitions and the concrete `CardDB` (one file per set; see card-data.md §4.1). The files of
the sets are generated from `data/cards/logical.json` by `scripts/gen_lean.py`: the official text
and the metadata of each card, and a part for the effect that is written by hand.
-/
