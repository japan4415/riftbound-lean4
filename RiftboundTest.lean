module

public import Riftbound
public import RiftboundTest.RulesVersion
public import RiftboundTest.Core
public import RiftboundTest.Actions
public import RiftboundTest.Setup
public import RiftboundTest.Turn
public import RiftboundTest.Resources
public import RiftboundTest.Trace
public import RiftboundTest.Fixtures
public import RiftboundTest.Deck
public import RiftboundTest.Tournament
public import RiftboundTest.Cards
public import RiftboundTest.IR

/-!
# RiftboundTest

Test driver for `lake test`. Tests are checked at build time (`#guard`, `example ... := by decide`).
-/
