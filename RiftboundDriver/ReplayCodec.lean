module

public import Lean.Elab.Deriving.FromToJson
public import Riftbound
public import RiftboundCards.BanList

/-!
# Lossless replay encoding

These codecs preserve engine inputs. The viewer's display JSON is independent of this format.
Keeping the instances in the driver leaves the rules and their proof dependencies unchanged.
-/

public section

open Lean Riftbound RiftboundCards

deriving instance ToJson, FromJson for
  CardId, SetCode, PlayerId, ObjId, Domain, PowerBucket, PowerSym, Cost, RunePool.Payment,
  SpellPick, CardTypeGuess, EffectAdd, Actor, RuneAbility, MoveDest, TriggerPayment, ActivationPayment,
  ActionKind, Action, ZoneKind, Zone, Phase, Event, GameResult,
  RulesDate, Mode, Riftbound.Format, EliminationGame, RuleSet, LegalityEnv, GameConfig,
  Deck, ConstructedDeck, LimitedDeck, ImplStatus, ConstructedFormat, RegionalSeason, BanListPeriod,
  MatchResult

end
