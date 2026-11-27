module

import RiftboundDriver.Trace
meta import RiftboundDriver.Trace
import RiftboundDriver.Replay
meta import RiftboundDriver.Replay
import RiftboundTest.CardLab
meta import RiftboundTest.CardLab

/-!
# Tests: the trace of a game (the viewer's input)
-/

namespace RiftboundTest

open Riftbound RiftboundDriver

-- An unfinished Cleanup can never appear as available neutral priority in the observed engine.
#guard (do
  let initial ← lab
  let p := initial.me
  let (board, victim) ← put initial p "OGN-051" .base
  let damaged := board.modObj victim (fun o => { o with damage := 10 })
  let (next, events) ← (advance 10 damaged []).toOption
  let (observed, _) ← (advanceWithDisclosures 10 damaged [] []).toOption
  let inTrash ← next.firstOf p .trash "OGN-051"
  return (advance 0 damaged []).toOption.isNone &&
    damaged.pending.head? == some (.priority p) && next.pending.head? == some (.priority p) &&
    next.countIn p .trash "OGN-051" == 1 && (cleanupStep next).isNone &&
    inTrash != victim && events.contains (.died inTrash p) && observed == (next, events) : Option Bool).getD false

-- A coded play records the specific Deflect sources and keeps an omitted choice ambiguous.
#guard (do
  let s ← lab
  let p := s.me
  let (s, spell) ← put s p "VEN-127" .hand
  let (s, target) ← put s s.you "VEN-064" .base
  let s := (s.noRunes p).setPool p { energy := 2, order := 1, fury := 1, any := 1 }
  let play (pick : SpellPick) : Action := ⟨.player p,
    .playCard spell ⟨2, [.order]⟩ [target] none none pick⟩
  let canonical := play .plain
  let explicit := play (.withDeflectPayment .plain [.flexible])
  let canonicalCode ← ReplayCardPlay.fromAction? s canonical
  let explicitCode ← ReplayCardPlay.fromAction? s explicit
  let encode (play : ReplayCardPlay) : ReplayAnswer := .observedCardPlay play
  let (next, events) ← (step 100 s explicit).toOption
  let json := actionJson explicit s.pending.head? (some next) events (some s)
  return canonicalCode.deflectPayment? == some [.domain .fury] &&
    explicitCode.deflectPayment? == some [.flexible] &&
    ((encode canonicalCode).resolveAt s 1).toOption == some (canonical, true) &&
    ((encode explicitCode).resolveAt s 1).toOption == some (explicit, true) &&
    ((encode { explicitCode with deflectPayment? := none }).resolveAt s 1).toOption.any (!·.2) &&
    ((encode { explicitCode with deflectPayment? := some [.domain .order] }).resolveAt s 1).isOk == false &&
    json.contains "\"deflectPayment\":[\"flexible\"]" : Option Bool).getD false

-- Older raw activations decode without Deflect allocation. Their JSON stays unchanged.
#guard (do
  let raw := "{\"actor\":{\"player\":{\"p\":{\"n\":1}}},\"kind\":{\"activate\":{\"costBanisher\":null,\"costObject\":null,\"discards\":[],\"idx\":1,\"pay\":{\"energy\":4,\"power\":[]},\"source\":{\"n\":57},\"targetPlayer\":null,\"targets\":[]}}}"
  let json ← (Lean.Json.parse raw).toOption
  let decoded ← (Lean.fromJson? json : Except String Action).toOption
  return decoded == ⟨.player ⟨1⟩, .activate ⟨57⟩ 1 ⟨4, [], none⟩ []⟩ &&
    (Lean.toJson decoded).compress == json.compress : Option Bool).getD false

-- Coded activations identify which payment reached the Chain and whether the evidence was unique.
#guard (do
  let s ← lab
  let p := s.me
  let (s, kingpin) ← put s p "UNL-001" .base
  let (s, target) ← put s s.you "OGN-013" .base
  let s := (s.noRunes p).setPool p { fury := 1, any := 1 }
  let canonical : Action := ⟨.player p, .activate kingpin 1 ⟨0, [], none⟩ [target]⟩
  let alternate : Action := ⟨.player p, .activate kingpin 1 ⟨0, [], some [.flexible]⟩ [target]⟩
  let ordinary ← ReplayAbilityUse.fromAction? s canonical
  let selected ← ReplayAbilityUse.fromAction? s alternate
  let encoded ← (Lean.fromJson? (Lean.toJson alternate) : Except String Action).toOption
  let resolve (activation : ReplayAbilityUse) := (ReplayAnswer.observedAbilityUse activation).resolveAt s 1
  let (next, events) ← (step 100 s alternate).toOption
  let json := actionJson alternate s.pending.head? (some next) events (some s)
  return encoded == alternate && ordinary.deflectPayment? == some [.domain .fury] &&
    selected.deflectPayment? == some [.flexible] &&
    (resolve ordinary).toOption == some (canonical, true) &&
    (resolve selected).toOption == some (alternate, true) &&
    (resolve { selected with deflectPayment? := none }).toOption.any (!·.2) &&
    !(resolve { selected with deflectPayment? := some [.domain .mind] }).isOk &&
    json.contains "\"deflectPayment\":[\"flexible\"]" : Option Bool).getD false

-- A coded trigger preserves both the declaration before funding and the final choice.
#guard (do
  let s ← lab
  let p := s.me
  let (s, mother) ← put s p "VEN-094" .hand
  let (s, ally) ← put s p "VEN-014" .base
  let (s, _) ← putAt (s.control p s.bf0) p "VEN-014" s.bf0
  let (s, sage) ← put (s.fund p 0) p "UNL-093" .base
  let (s, rune) ← put s p "OGN-007" .base
  let s := (s.modObj sage (fun o => { o with exhausted := false })).modObj rune
    (fun o => { o with exhausted := false })
  let awaiting := { s with pending := [.discard p 1] }
  let (offered, _) ← (step 100 awaiting ⟨.player p, .discardPick mother⟩).toOption
  let prepare : Action := ⟨.player p, .prepareTrigger 0 [ally] (.pay [])⟩
  let decline : Action := ⟨.player p, .putTrigger 0 [] .skip⟩
  let (locked, _) ← (step 100 offered prepare).toOption
  let useSage : Action := ⟨.player p, .triggerAdd (.ability sage 0 0 [])⟩
  let useRune : Action := ⟨.player p, .triggerAdd (.rune rune false)⟩
  let namedSage ← ReplayAbilityUse.fromAction? locked useSage
  let namedRune ← ReplayCardPick.fromAction? locked useRune
  let (funded, _) ← (step 100 locked useSage).toOption
  let finalize : Action := ⟨.player p, .putTrigger 0 [ally]⟩
  let namedPrepare ← ReplayTriggerUse.fromAction? offered prepare
  let namedDecline ← ReplayTriggerUse.fromAction? offered decline
  let namedFinalize ← ReplayTriggerUse.fromAction? funded finalize
  let answer (trigger : ReplayTriggerUse) := ReplayAnswer.observedTriggerUse trigger
  let (resolved, _) ← (step 100 funded finalize).toOption
  let undecided := { namedPrepare with targets := [{ card := cid "VEN-014" }] }
  let decoded ← (Lean.fromJson? (Lean.toJson (answer namedFinalize)) : Except String ReplayAnswer).toOption
  return namedPrepare.stage == .prepare && namedPrepare.source == cid "VEN-094" &&
    namedDecline.stage == .decline && namedFinalize.stage == .finalize &&
    namedSage.kind == .triggerAdd && namedRune.kind == .triggerRuneExhaust &&
    ((ReplayAnswer.observedAbilityUse namedSage).resolveAt locked 2).toOption == some (useSage, true) &&
    ((ReplayAnswer.observedCardPick namedRune).resolveAt locked 2).toOption == some (useRune, true) &&
    ((answer namedPrepare).resolveAt offered 1).toOption == some (prepare, true) &&
    ((answer namedDecline).resolveAt offered 1).toOption == some (decline, true) &&
    (decoded.resolveAt funded 3).toOption == some (finalize, true) &&
    ((answer undecided).resolveAt offered 1).toOption.any (!·.2) &&
    !((answer { namedFinalize with source := cid "VEN-014" }).resolveAt funded 3).isOk &&
    ((ReplayAnswer.inferredTriggerUse namedFinalize "ability seen after payment").resolveAt funded 3).toOption ==
      some (finalize, false) &&
    (settleChain {} 12 resolved).mightNow ally == some 4 : Option Bool).getD false

-- Two delayed triggers from a departed Spell can be distinguished by the damaged Units.
#guard (do
  let s ← lab
  let p := s.me
  let (s, decree) ← put s p "OGN-221" .hand
  let (s, ally) ← put s p "OGN-001" .base
  let (s, foe) ← put s s.you "OGN-116" .base
  let registered ← play s p decree
  let (damaged, events) := dealAll registered [(ally, 1), (foe, 1)]
  let (waiting, _) ← (advance 100 (damaged.withTriggers events) []).toOption
  let first : Action := ⟨.player p, .putTrigger 0 []⟩
  let second : Action := ⟨.player p, .putTrigger 1 []⟩
  let a ← ReplayTriggerUse.fromAction? waiting first
  let b ← ReplayTriggerUse.fromAction? waiting second
  let resolve (trigger : ReplayTriggerUse) := (ReplayAnswer.observedTriggerUse trigger).resolveAt waiting 1
  return a.source == cid "OGN-221" && b.source == a.source &&
    a.sourceObject?.isNone && b.sourceObject?.isNone &&
    a.subject?.isSome && b.subject?.isSome && a.subject? != b.subject? &&
    (resolve a).toOption == some (first, true) && (resolve b).toOption == some (second, true) &&
    (resolve { a with subject? := none }).toOption.any (!·.2) : Option Bool).getD false

/-- The trace of the demo game, or the error text. -/
meta def traceOf (seed turns : Nat) : String :=
  match demoTrace seed turns with | .ok j => j | .error e => "ERROR " ++ e

-- the trace is written, and it is the same each time: a seed replays a game
#guard !(traceOf 1 2).startsWith "ERROR"
#guard traceOf 1 2 == traceOf 1 2
#guard traceOf 1 2 != traceOf 2 2

-- it names its parts, and a longer game is a longer trace
#guard (traceOf 1 2).startsWith "{\"seed\":1,\"players\":2,\"cards\":{"
#guard ((traceOf 1 2).splitOn "\"steps\":[").length == 2
#guard (traceOf 1 4).length > (traceOf 1 2).length

-- a demo game is played to the end: a player wins by points (CR 323.1)
#guard (traceOf 1 40).contains '{' && ((traceOf 1 40).splitOn "\"won\":[").length == 2

-- the trace shows the Battlefields and the Units at them
#guard ((traceOf 1 12).splitOn "\"battlefields\":[{").length > 2
#guard ((traceOf 1 12).splitOn "\"t\":\"moved_unit\"").length > 1
#guard ((traceOf 1 12).splitOn "\"t\":\"scored\"").length > 1

-- The full trace records public XP in seat order as it is gained and spent.
#guard (do
    let s ← lab
    let gained := gainXPOf 3 (gainXPOf 2 s ⟨1⟩) ⟨0⟩
    let (before, seen) := stateJson gained {}
    let (after, _) := stateJson (gained.spendXP ⟨0⟩ 1) seen
    return (before.splitOn "\"xp\":[3,2]").length == 2 &&
      (after.splitOn "\"xp\":[2,2]").length == 2 : Option Bool).getD false

-- Each observed balance uses its own resource kind and the specified seat's Pool.
#guard (do
  let s ← lab
  let s := s.setPool s.me
    { energy := 1, unitEnergy := 2, spellEnergy := 3, mind := 4, order := 5, any := 6 }
  let check (facts : List ReplayObservationFact) :=
    (ReplayObservation.checkAt [{ checkpoint := 7, source? := some "Pool on screen", facts }] 7 s).isOk
  return check [.poolResource s.me .energy 1, .poolResource s.me .unitEnergy 2,
      .poolResource s.me .spellEnergy 3, .poolResource s.me (.domainPower .mind) 4,
      .poolResource s.me (.domainPower .order) 5, .poolResource s.me .anyPower 6,
      .poolResource s.you .energy 0] &&
    !check [.poolResource s.you .spellEnergy 3] &&
    !check [.poolResource s.me (.domainPower .fury) 4] &&
    !check [.poolResource ⟨s.playerCount⟩ .energy 0] : Option Bool).getD false

-- A played card still has its recorded code if it moved again within the same answer.
#guard (do
  let s ← lab
  let p := s.me
  let (s, original) ← put s p "OGN-051" .base
  let dest := Zone.player p .trash
  let (s, moved) ← moveObj s original dest
  let events : List Event := [.played p original, .moved original moved dest, .drew s.you]
  let check (sequence : List ReplayPublicEvent) :=
    (ReplayObservation.checkAt [{ checkpoint := 1, facts := [.eventsInOrder sequence] }] 1 s events).isOk
  return check [.playedCard p, .drew s.you] && check [.playedCardCode p (cid "OGN-051"), .drew s.you] &&
    !check [.playedCardCode p (cid "OGN-001")] && !check [.drew s.you, .playedCard p] &&
    !check [.playedCard p, .playedCardCode p (cid "OGN-051")] : Option Bool).getD false

-- Lethal damage and death remain identifiable after the Unit gets a new Trash ID.
#guard (do
  let s ← lab
  let p := s.me
  let (s, unit) ← put s p "OGN-051" .base
  let (dead, death) := killObj s unit
  let events : List Event := [.damaged unit 8] ++ death
  let code := cid "OGN-051"
  let check (sequence : List ReplayPublicEvent) :=
    (ReplayObservation.checkAt [{ checkpoint := 1, facts := [.eventsInOrder sequence] }]
      1 dead events).isOk
  return check [.damagedCard code 8, .diedCard p code] &&
    check [.damaged 8, .died p] && !check [.died p, .damaged 8] &&
    !check [.damaged 7] && !check [.diedCard s.you code] &&
    !check [.damagedCard (cid "OGN-001") 8] && !check [.died p, .diedCard p code]
  : Option Bool).getD false

-- A token can disappear in the same answer. Its public death still has a visible identity.
#guard (do
  let s ← lab
  let p := s.me
  let code := tokenId "Recruit"
  let (before, token) ← addObject s
    { kind := .token code, owner := p, controller := p, timestamp := ⟨0⟩ } (.player p .base)
  let (trash, events) := killObj before token
  let dead ← events.findSome? (fun | .died id _ => some id | _ => none)
  let after ← removeObj trash dead
  let evidence : ReplayObservation := { checkpoint := 1, facts := [.eventsInOrder [
    .damagedCard code 1, .diedCard p code]] }
  let events := .damaged token 1 :: events
  return (after.obj? dead).isNone &&
    (ReplayObservation.checkAt [evidence] 1 after events (before := some before)).isOk &&
    (ReplayObservation.checkAt [evidence] 1 after events).isOk == false
  : Option Bool).getD false

-- XP is seat-specific, and marker observations retain all copies of a matching Unit.
#guard (do
  let s ← lab
  let p := s.me
  let (s, first) ← put s p "OGN-051" .base
  let (s, second) ← put s p "OGN-051" .base
  let (s, _) ← put s p "OGN-049" .base
  let (s, _) ← put s s.you "OGN-051" .base
  let s := (s.modObj first (fun o => { o with buffed := true })).modObj second
    (fun o => { o with buffed := true, stunned := true })
  let s := gainXPOf 3 s p
  let card := cid "OGN-051"
  let check (facts : List ReplayObservationFact) :=
    (ReplayObservation.checkAt [{ checkpoint := 1, facts }] 1 s).isOk
  return check [.xp p 3, .xp s.you 0, .markedUnits p .base .buffed [card, card],
      .markedUnits p .base .stunned [card], .markedUnits s.you .base .buffed []] &&
    !check [.xp p 2] && !check [.markedUnits p .base .buffed [card]] &&
    !check [.markedUnits p .base .stunned [card, card]] : Option Bool).getD false

-- Current Might is checked per Unit, including two copies with different modifiers.
#guard (do
  let s ← lab
  let p := s.me
  let q := s.you
  let (s, first) ← put s p "OGN-136" .base
  let (s, _) ← put s p "OGN-136" .base
  let (s, _) ← put s q "OGN-136" .base
  let s := s.modObj first (fun o => { o with buffed := true })
  let card := cid "OGN-136"
  let check (who : PlayerId) (units : List ReplayObservedUnitMight) :=
    (ReplayObservation.checkAt [{ checkpoint := 1, facts := [.unitMights who .base units] }] 1 s).isOk
  return check p [⟨card, 3⟩, ⟨card, 2⟩] && check p [⟨card, 2⟩, ⟨card, 3⟩] &&
    check q [⟨card, 2⟩] && !check p [⟨card, 3⟩, ⟨card, 3⟩] &&
    !check p [⟨card, 3⟩] : Option Bool).getD false

-- A token already known to the viewer changes identity in `copies`, using its original ID.
#guard (do
    let s ← lab
    let (s, model) ← put s s.you "UNL-111" .base
    let id : ObjId := ⟨s.nextId⟩
    let placed := createOne (cid "UNL-T06") s.me none true s
    let (before, seen) := stateJson placed {}
    let copied := (becomeCopyOf model placed id).1
    let (after, _) := stateJson copied seen
    return (before.splitOn (s!"\"{id.n}\":" ++ "{\"card\":\"UNL-T06\"")).length == 2 &&
      (after.splitOn ("\"copies\":{" ++ s!"\"{id.n}\":\"UNL-111\"" ++ "}")).length == 2 &&
      (after.splitOn "\"new\":{}").length == 2 : Option Bool).getD false

-- A revised replacement still identifies the affected Unit and the actual Gear selected.
#guard
  let choose := Effect.recordDeathReselection [⟨3⟩, ⟨5⟩] [⟨3⟩] ⟨5⟩
  let frame := Frame.eitherDo ⟨1⟩ ⟨5⟩ {} (choose (.gear ⟨10⟩)) (choose (.gear ⟨11⟩)) .nil
  deathReplacementFields (some frame) false == [("deathGearUnit", "5"), ("deathGearSource", "11")]

-- The trace distinguishes the original Kill from a new Kill of the same Unit.
#guard
  let choose := Effect.recordNestedDeathDecision ⟨5⟩ [(⟨5⟩, false)] ⟨5⟩
  let frame := Frame.eitherDo ⟨1⟩ ⟨5⟩ {} (choose (.gear ⟨10⟩) none) (choose (.gear ⟨11⟩) none) .nil
  deathReplacementFields (some frame) true ==
    [("deathRootUnit", "5"), ("deathDepth", "1"), ("deathGearUnit", "5"), ("deathGearSource", "10")]

-- A combat priority choice identifies the Unit and the selected keyword.
#guard
  let record (priority : CombatAssignmentPriority) :=
    Effect.prim (.markOn .self (.combatAssignmentPriority priority))
  let frame := Frame.eitherDo ⟨0⟩ ⟨5⟩ {} (record .tank) (record .backline) .nil
  combatPriorityFields (some frame) true ==
      [("combatPriorityUnit", "5"), ("combatAssignmentPriority", jstr "tank")] &&
    combatPriorityFields (some frame) false ==
      [("combatPriorityUnit", "5"), ("combatAssignmentPriority", jstr "backline")]

-- quotes and backslashes in a name are escaped
#guard jstr "a\"b\\c" == "\"a\\\"b\\\\c\""
#guard jarr ["1", "2"] == "[1,2]"
#guard jobj [("k", "1")] == "{\"k\":1}"

end RiftboundTest
