module

public import Std.Data.HashSet
public import RiftboundDriver.Run
public import RiftboundDriver.Demo

/-!
# Driver: the trace of a game

Plays a game with the engine and writes down every answer as JSON: the answer, the events it
caused, and the state after it. A viewer replays the file as an animation (`viewer/`). The viewer
has no rules of its own: everything it shows was computed by `step`. This library is not part of
the verified core, so the JSON written here is not covered by the proofs (design.md §4).
-/

@[expose] public section

namespace RiftboundDriver

open Riftbound

/-- A JSON string. Quotes, backslashes and line breaks are escaped. -/
def jstr (s : String) : String :=
  let s1 := ((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n"
  "\"" ++ (s1.replace "\r" "\\r").replace "\t" "\\t" ++ "\""

/-- A JSON array of already written items. -/
def jarr (l : List String) : String := "[" ++ ",".intercalate l ++ "]"

/-- A JSON object of already written values. -/
def jobj (l : List (String × String)) : String :=
  "{" ++ ",".intercalate (l.map fun (k, v) => jstr k ++ ":" ++ v) ++ "}"

/-- The last part of a dotted name: `Riftbound.Phase.main` is `main`. -/
def lastSeg (s : String) : String := (s.splitOn ".").getLast?.getD s

/-- The name of a constructor, from its `Repr`. -/
def ctorName {α : Type} [Repr α] (a : α) : String :=
  lastSeg (((reprStr a).takeWhile (fun c => !c.isWhitespace)).toString)

/-- A zone as text: `p0.hand`, `battlefield`, `chain`. -/
def zoneName : Zone → String
  | .player p k => s!"p{p.n}.{ctorName k}"
  | .battlefieldZone => "battlefield"
  | .chain => "chain"

/-- A cost as JSON: the Energy, and the Power symbols (a domain, `any`, or `own` for the domain of
the card). -/
def costJson (k : Cost) : String :=
  jobj [("energy", toString k.energy),
    ("power", jarr (k.power.map (fun s => match s with
      | .domain d => jstr (ctorName d) | .any => jstr "any" | .own => jstr "own")))]

/-- The chosen token placement, or the decision to see the remaining locations. -/
def tokenLocationFields (frame : Option Frame) (yes : Bool) : List (String × String) :=
  match frame with
  | some (.eitherDo _ _ _ a@(.prim (.playUnitTokenAt name _)) b _) =>
    match if yes then a else b with
    | .prim (.playUnitTokenAt _ dest) =>
      [("token", jstr name), ("dest", dest.elim "null" (fun bf => toString bf.n))]
    | .eitherOf _ => [("token", jstr name), ("moreLocations", "true")]
    | _ => []
  | _ => []

/-- Serialize the destination and costs chosen for a permanent played by an effect. -/
def reducedPlayFields (card : ObjId) (plan : ReducedPermanentPlay) : List (String × String) :=
  [("card", toString card.n), ("cost", costJson plan.cost),
    ("destination", plan.battlefield.elim "null" (fun id => toString id.n)),
    ("additionalPaid", if plan.additionalPaid then "true" else "false"),
    ("accelerated", if plan.accelerated then "true" else "false")] ++
    (if plan.battlefieldFees.isEmpty then [] else
      [("battlefieldFees", jarr (plan.battlefieldFees.map (fun id => toString id.n)))]) ++
    (if plan.gearDiscounts.isEmpty then [] else
      [("gearDiscounts", jarr (plan.gearDiscounts.map (fun id => toString id.n)))]) ++
    plan.extraObject.toList.map (fun id => ("extraObject", toString id.n)) ++
    plan.discard.toList.map (fun id => ("discard", toString id.n)) ++
    plan.showOff.toList.map (fun id => ("showOff", toString id.n))

/-- Identify an individual Add activation in a permanent's payment. -/
def effectAddJson : EffectAdd → String
  | .rune id recycle => jobj [("source", toString id.n),
    ("rune", jstr (if recycle then "recycle" else "exhaust"))]
  | .ability id idx energy power banish => jobj
    ([("source", toString id.n), ("idx", toString idx), ("cost", costJson ⟨energy, power.map PowerSym.domain⟩)] ++
      banish.toList.map (fun card => ("banishCostCard", toString card.n)))

/-- Serialize an Add the player can choose and the activations they have already chosen. -/
def nextEffectAddFields (cost : Cost) (adds : List EffectAdd) (add : EffectAdd) :
    List (String × String) :=
  [("playAdd", effectAddJson add), ("playPaymentCost", costJson cost),
    ("preparedAdds", jarr (adds.dropLast.map effectAddJson))]

/-- Describe a pending payment, including activations already chosen for that payment. -/
def reducedPlayDecision (effect : Effect) (funding : Bool) : List (String × String) :=
  match effect with
  | .finishReducedPermanent card _ plan => [("reducedPlay", jobj (reducedPlayFields card plan))]
  | .finishFundedPermanent card _ plan adds =>
    [("reducedPlay", jobj (reducedPlayFields card plan)),
      ("preparedAdds", jarr (adds.map effectAddJson))]
  | .fundPermanentFromEffect card _ plan adds =>
    match adds.getLast? with
    | none => [("reducedPlay", jobj (reducedPlayFields card plan)), ("choosePlayPayment", "true")]
    | some add => nextEffectAddFields plan.cost adds add
  | .eitherOf _ => [(if funding then "morePlayPayments" else "morePlayOptions", "true")]
  | .nop => [("declinePlay", "true")]
  | _ => []

/-- Choices of payment and destination when a Unit or Gear is played by an effect. -/
def reducedPermanentFields (frame : Option Frame) (yes : Bool) : List (String × String) :=
  match frame with
  | some (.mayDo _ _ _ (.chooseLookedToPlay ..) _) => [("lookedPlay", "true")]
  | some (.eitherDo _ _ _ a@(.finishReducedPermanent ..) b _) =>
    reducedPlayDecision (if yes then a else b) false
  | some (.eitherDo _ _ _ a@(.finishFundedPermanent ..) b _) =>
    reducedPlayDecision (if yes then a else b) true
  | some (.eitherDo _ _ _ a@(.fundPermanentFromEffect _ _ _ adds) b _) =>
    reducedPlayDecision (if yes then a else b) (!adds.isEmpty)
  | _ => []

/-- Identify a decision to apply an optional Empower. -/
def empowerChoiceFields (frame : Option Frame) : List (String × String) :=
  match frame with
  | some (.mayDo _ _ _ (.prim (.empower _)) _) => [("empowerOffer", "true")]
  | _ => []

/-- Encode a mode number and its display name when known. -/
def modeFields (definition : Option EffectDef) (i : Nat) : List (String × String) :=
  let label := definition.bind (fun e => (e.modes[i]?).map SpellMode.label)
  [("mode", toString i)] ++ label.toList.map (fun name => ("modeLabel", jstr name))

/-- Label the portions of a Unit or Gear's optional payment that the player elected. -/
def permanentCostFields (definition : Option CardDef) (own : List Nat) : List (String × String) :=
  let printed := definition.any (·.additionalCost.isSome)
  (if printed then [("additionalCostPaid", if own.contains 0 then "true" else "false")] else []) ++
    (if definition.any (·.hasKeyword .accelerate) then
      [("accelerated", if own.contains (if printed then 1 else 0) then "true" else "false")]
    else [])

/-- Encode the finalization choice separately from the targeted objects. -/
def spellPickFields (state : Option GameState) (c : ObjId) : SpellPick → List (String × String)
  | .plain => []
  | .mode i => modeFields (state.bind (fun s => (s.cardDef? c).bind CardDef.spellEffect)) i
  | .destination bf => [("moveDest", bf.elim "null" (fun id => toString id.n))]
  | .modeDestination i bf =>
    modeFields (state.bind (fun s => (s.cardDef? c).bind CardDef.spellEffect)) i ++
      [("moveDest", bf.elim "null" (fun id => toString id.n))]
  | .payForBattlefield sources own =>
    [("battlefieldFees", jarr (sources.map (fun id => toString id.n)))] ++
      permanentCostFields (state.bind (·.cardDef? c)) own
  | .withPermanentCosts own => permanentCostFields (state.bind (·.cardDef? c)) own
  | .withGearDiscounts pick sources =>
    spellPickFields state c pick ++ [("gearDiscounts", jarr (sources.map (fun id => toString id.n)))]
  | .withPlayer pick player =>
    spellPickFields state c pick ++ [("targetPlayer", toString player.n)]
  | .withShowOff pick object =>
    spellPickFields state c pick ++ [("showOff", toString object.n)]
  | .withExtraObject pick object =>
    spellPickFields state c pick ++ [("extraCostObject", toString object.n)]
  | .withSpellExhausts pick groups =>
    let payers := groups.flatMap (fun (legend, units) => legend :: units)
    spellPickFields state c pick ++ [("spellExhaustPayers", jarr (payers.map (fun id => toString id.n)))]
  | .thenRepeat pick _ _ => spellPickFields state c pick
  | .withVariablePower pick n =>
    spellPickFields state c pick ++ [("variablePower", toString n)]
  | .withCosts pick printed repeats =>
    spellPickFields state c pick ++
      [("additionalCostPaid", if printed then "true" else "false"), ("repeatsPaid", toString repeats)]

/-- Describe one of the replacement effects that can be chosen next. -/
def damageReplacementFields (unit : ObjId) (replacement : DamageReplacement) : List (String × String) :=
  let (kind, extra) := match replacement with
    | .double => ("double", [])
    | .prevent _ value => ("prevent", [("preventValue", toString value)])
    | .shield _ => ("shield", [])
  [("unit", toString unit.n), ("damageReplacement", jstr kind)] ++ extra

/-- The order the affected Unit's controller chooses for damage replacement. -/
def damageOrderFields (frame : Option Frame) (yes : Bool) : List (String × String) :=
  match frame with
  | some (.eitherDo _ _ _ first@(.chooseDamageReplacement ..) other _)
  | some (.eitherDo _ _ _ first@(.orderCombatDamage ..) other _) =>
    match if yes then first else other with
    | .chooseDamageReplacement _ hit replacement =>
      damageReplacementFields hit.target replacement ++ [("incomingDamage", toString hit.amount)]
    | .orderCombatDamage unit (replacement :: _) _ =>
      damageReplacementFields unit replacement ++ [("combatDamageOrder", "true")]
    | _ => [("moreDamageReplacements", "true")]
  | _ => []

/-- Describe the allocation selected for split damage (CR 355.14). -/
def damageDivisionFields (frame : Option Frame) (yes : Bool) : List (String × String) :=
  match frame with
  | some (.eitherDo _ _ _ first@(.applySplitDamage _) other _) =>
    match if yes then first else other with
    | .applySplitDamage hits =>
      [("damageDivision", jarr (hits.map (fun (unit, amount) =>
        jobj [("unit", toString unit.n), ("amount", toString amount)])))]
    | _ => [("moreDamageDivisions", "true")]
  | _ => []

/-- Describe whose effect can replace this Unit's pending death (CR 372). -/
def deathBanishFields (frame : Option Frame) (yes : Bool) : List (String × String) :=
  match frame with
  | some (.eitherDo _ unit _ first@(.chooseDeathBanisher ..) other _) =>
    [("banishDeathUnit", toString unit.n)] ++
      (match if yes then first else other with
      | .chooseDeathBanisher _ player => [("banishingPlayer", toString player.n)]
      | _ => [])
  | _ => []

/-- Identify the affected Unit and the exact sacrifice elected during its death replacement. -/
def deathSacrificeFields (frame : Option Frame) (yes : Bool) : List (String × String) :=
  match frame with
  | some (.eitherDo _ _ _ first@(.recordDeathSacrifice unit _) other _) =>
    [("deathSacrificeUnit", toString unit.n)] ++
      (match if yes then first else other with
      | .recordDeathSacrifice _ cost =>
        [("deathSacrificeCost", cost.elim "null" (fun id => toString id.n))]
      | _ => [])
  | _ => []

/-- Identify the replacement that the controller puts next. -/
def deathOrderFields (frame : Option Frame) (yes : Bool) : List (String × String) :=
  match frame with
  | some (.eitherDo _ _ _ first@(.recordDeathOrder ..) other _) =>
    match if yes then first else other with
    | .recordDeathOrder _ unit => [("deathOrderUnit", toString unit.n)]
    | _ => [("moreDeathOrders", "true")]
  | _ => []

/-- Describe a decision about paying during resolution, including individual payments. -/
def effectPaymentFields (state : Option GameState) (frame : Option Frame)
    (yes : Bool) : List (String × String) :=
  match frame with
  | some (.eitherDo p src env (.payThen cost _) other _) =>
    let target := match other with
      | .prim (.counter (.slot i)) => env.slots[i]?.bind (fun
        | .obj id => some id
        | _ => none)
      | .prim (.counter sel) => state.bind (fun s => (sel.eval s p src env).bind List.head?)
      | _ => none
    [("effectCost", costJson cost)] ++
      target.toList.map (fun id => ("spellPaymentTarget", toString id.n))
  | some (.eitherDo _ _ _ first@(.paySelected ..) other _) =>
    match if yes then first else other with
    | .paySelected cost _ _ => [("effectPaymentPlan", costJson cost)]
    | _ => [("moreEffectPayments", "true")]
  | _ => []

/-- Encode the targets together with their controllers for the viewer. -/
def spellTargetFields (state : Option GameState) (targets : List ObjId) : List (String × String) :=
  let controllers := targets.map (fun id =>
    (state.bind (·.obj? id)).elim "null" (fun o => toString o.controller.n))
  [("targets", jarr (targets.map (fun id => toString id.n))),
    ("targetControllers", jarr controllers)]

/-- Record targets beside the mode and destination for each execution of a repeated Spell. -/
def spellExecutionFields (state : Option GameState) (card : ObjId) (pick : SpellPick)
    (targets : List ObjId) : List (String × String) :=
  if pick.hasExecutionChoices then
    [("repeatExecutions", jarr ((pick.executions targets).map (fun (choice, ts) =>
      jobj (spellTargetFields state ts ++ spellPickFields state card choice))))]
  else []

/-- Describe whether to choose again, and the new finalization choices on offer (CR 750-755). -/
def remakeSpellFields (state : Option GameState) (frame : Option Frame)
    (yes : Bool) : List (String × String) :=
  match frame with
  | some (.mayDo _ _ _ (.eitherOf (.cons (.setSpellChoices spell _ _) _)) _) =>
    [("remakeSpell", toString spell.n)]
  | some (.eitherDo _ _ _ first@(.setSpellChoices spell _ _) other _) =>
    match if yes then first else other with
    | .setSpellChoices item pick targets =>
      [("remadeSpell", toString item.n)] ++ spellTargetFields state targets ++
        spellPickFields state item pick ++ spellExecutionFields state item pick targets
    | _ => [("moreSpellChoices", toString spell.n)]
  | _ => []

/-- Describe the play and cost of the chosen Spell. -/
def effectSpellPlayFields (state : Option GameState) (card : ObjId) (plan : EffectSpellPlay) :
    List (String × String) :=
  [("queuedSpell", toString card.n), ("queuedCost", costJson plan.cost)] ++
    spellTargetFields state plan.targets ++ spellPickFields state card plan.pick ++
    spellExecutionFields state card plan.pick plan.targets ++
    (if plan.discard.isSome || (state.bind (·.cardDef? card)).any (·.discardToPlay) then
      [("playDiscard", plan.discard.elim "null" (fun id => toString id.n))]
    else [])

/-- A Spell played by an effect: its targets, payment or cancellation. -/
def effectSpellDecision (state : Option GameState) : Effect → List (String × String)
  | .finishLimitedSpell card plan adds =>
    effectSpellPlayFields state card plan ++
    (if adds.isEmpty then [] else [("preparedAdds", jarr (adds.map effectAddJson))])
  | .fundLimitedSpell card plan adds =>
    match adds.getLast? with
    | none => effectSpellPlayFields state card plan ++ [("chooseSpellPayment", "true")]
    | some add => nextEffectAddFields plan.cost adds add
  | .cancelLimitedSpell _ => [("declinePlay", "true")]
  | _ => [("moreTrashSpellChoices", "true")]

/-- Describe an active choice for a Spell played by an effect. -/
def effectSpellFields (state : Option GameState) (frame : Option Frame)
    (yes : Bool) : List (String × String) :=
  match frame with
  | some (.mayDo _ _ _ (.prim (.castInline _)) _) => [("trashSpellOffer", "true")]
  | some (.mayDo _ _ _ (.prim (.playReduced (.pick .one _ .inMainDeck _) _ none)) _) =>
    [("revealedPlayOffer", "true")]
  | some (.eitherDo _ _ _ first@(.finishLimitedSpell ..) other _)
  | some (.eitherDo _ _ _ first@(.fundLimitedSpell ..) other _) =>
    effectSpellDecision state (if yes then first else other)
  | _ => []

/-- A payment's Banish replacement, naming the affected card and the player whose effect applies. -/
def costBanishJson (unit : ObjId) (player : PlayerId) : String :=
  jobj [("player", toString player.n), ("unit", toString unit.n)]

/-- The Banish replacements shown for the objects committed as a trigger's cost. -/
def triggerCostBanishes (state : Option GameState) (ids : List ObjId)
    (chosen : List (ObjId × PlayerId)) (events : List Event) : List String :=
  ids.filterMap (fun id =>
    let recorded := events.findSome? (fun
      | .moved from_ next (.player _ .banishment) => if from_ == id then some next else none
      | _ => none)
    let applied := recorded.bind (fun next => events.findSome? (fun
      | .banished player _ card => if card == next then some player else none
      | _ => none))
    let declared := chosen.findSome? (fun (card, player) => if card == id then some player else none)
    let automatic := state.bind (fun s =>
      if (s.deathSaver id).isSome then none else
        s.banishOnDeathBy id <|> ((s.obj? id).filter (s.replacesTrash id)).map (·.owner))
    (applied <|> declared <|> automatic).map (costBanishJson id))

/-- JSON fields shared by individual and simultaneous Standard Moves. -/
def moveFields (dest : MoveDest) (pay : Cost) : List (String × String) :=
  [("dest", match dest with | .base => "null" | .battlefield bf => toString bf.n)] ++
    (if pay == Cost.zero then [] else [("movePayment", costJson pay)])

/-- An action as JSON, with any context needed to describe the choice. -/
def actionJson (a : Action) (frame : Option Frame := none)
    (state : Option GameState := none) (events : List Event := []) : String :=
  let who := match a.actor with
    | .player p => s!"p{p.n}"
    | .chance => "chance"
    | .clock => "clock"
    | .judge => "judge"
  let kind := ctorName a.kind
  let extra : List (String × String) := match a.kind with
    | .timeCalled =>
      if state.any (fun s => match s.config.ruleSet with
          | .tournamentElimination .. => true
          | _ => false) then [("singleElimination", "true")] else []
    | .runeAbility c ab => [("card", toString c.n), ("ability", jstr (ctorName ab))]
    | .playCard c pay ts flow discard pick =>
      let played := (events.findSome? (fun
        | .moved before after _ => if before == c then some after else none
        | _ => none)).getD c
      let battlefield := state.bind (fun s =>
        if (s.cardDef? played).any (fun d => d.hasType .unit && !d.hasType .spell) then s.bfPick ts else none)
      let hidden := state.any (fun s =>
        (s.obj? played).any (fun o => o.fromHidden || s.playingFromHidden o.owner c))
      [("card", toString c.n), ("pay", toString (pay.energy + pay.power.length)),
        ("power", jarr (pay.power.map (fun d => jstr (ctorName d)))),
        ("targets", jarr (ts.map (fun t => toString t.n)))] ++
        (flow.toList.map (fun k => ("flowCost", costJson k))) ++
        (discard.toList.map (fun o => ("discards", jarr [toString o.n]))) ++
        (battlefield.toList.map (fun id => ("playDestination", toString id.n))) ++
        (if hidden then [("hiddenPlay", "true")] else []) ++
        spellPickFields state played pick ++ spellExecutionFields state played pick ts
    | .standardMove u d pay => [("unit", toString u.n)] ++ moveFields d pay
    | .startGroupMove d pay => moveFields d pay
    | .assignPick u => [("unit", toString u.n)]
    | .manaAbility src idx pay banish =>
      let restricted := match state.bind (fun s => s.manaOffer src idx) with
        | some (_, _, .unitEnergy n) => [("unitEnergyAdded", toString n)]
        | some (_, _, .permanent) => [("permanentPowerAdded", "1")]
        | _ => []
      [("source", toString src.n), ("index", toString idx), ("energy", toString pay.energy),
       ("power", jarr (pay.power.map (fun d => jstr (ctorName d))))] ++ restricted ++
        banish.toList.map (fun card => ("banishCostCard", toString card.n))
    | .putTrigger i ts payment | .prepareTrigger i ts payment =>
      let trigger : Option PendTrigger := match frame with
        | some (.triggerOrder _ t more _ _) => (t :: more)[i]?
        | _ => none
      let plan := match frame with
        | some (.triggerOrder _ _ _ _ funding) => funding
        | _ => none
      let source := trigger.map PendTrigger.source
      let resources := (state.bind (fun s => trigger.map (fun t => triggerPrice s t ts))).toList.flatMap
        (fun price => if price.power.isEmpty then [] else [("triggerDeflect", toString price.power.length)])
      [("index", toString i), ("targets", jarr (ts.map (fun t => toString t.n)))] ++ resources ++
      plan.toList.map (fun p => ("triggerPreparedAdds", jarr (p.adds.map effectAddJson))) ++
      (source.toList.map (fun id => ("source", toString id.n))) ++
      (match payment with
       | .skip => [("decline", "true")]
       | .pay ids mode player banishers =>
         let costs := match state, trigger with
           | some s, some t =>
             if mode.isNone && player.isNone && ts.isEmpty && !trigOptional s t &&
                 (!(trigChoices s t).isEmpty || !(trigModes s t).contains none ||
                   !(trigPlayerOptions s t).contains none) then
               [("unavailable", "true")]
             else match trigCost s t with
               | .energy n => [("energy", toString n)]
               | .burn n => [("burn", toString n)]
               | .exhaustSelf => [("exhaustSource", "true")]
               | _ => []
           | _, _ => []
         let definition := state.bind (fun s => trigger.bind (fun t => abilityDef s t.card t.idx))
         let replacements := triggerCostBanishes state ids banishers events
         mode.toList.flatMap (modeFields definition) ++ costs ++
           player.toList.map (fun p => ("targetPlayer", toString p.n)) ++
           (if replacements.isEmpty then [] else [("costBanishes", jarr replacements)]) ++
           (if ids.isEmpty then [] else [("sacrifices", jarr (ids.map (fun id => toString id.n)))]))
    | .triggerAdd add =>
      [("playAdd", effectAddJson add)] ++
        (match frame with
        | some (.triggerOrder _ _ _ _ (some plan)) =>
          [("triggerPreparedAdds", jarr (plan.adds.map effectAddJson))]
        | _ => [])
    | .activate src idx pay ts discards targetPlayer costBanisher costObject =>
      [("source", toString src.n), ("index", toString idx),
       ("pay", toString (pay.energy + pay.power.length)),
       ("power", jarr (pay.power.map (fun d => jstr (ctorName d)))),
       ("targets", jarr (ts.map (fun t => toString t.n)))] ++
      (if discards.isEmpty then [] else [("discards", jarr (discards.map (fun id => toString id.n)))]) ++
      targetPlayer.toList.map (fun q => ("targetPlayer", toString q.n)) ++
      (costBanisher.toList.flatMap (fun who => (costObject <|> ts.getLast?).toList.map (fun unit =>
        ("costBanish", costBanishJson unit who)))) ++
      (match state.bind (fun s => s.activationAt src idx) with
      | some (grant, .activated costs _ e _) =>
        (match permanentCost costs, costObject with
        | some (.exhaust, _), some id => [("exhaustCostObject", toString id.n)]
        | some (.kill, _), some id => [("killCostObject", toString id.n)]
        | _, _ => []) ++
        (if grant.isSome && e.body == .prim (.ready .self) then
          [("abilityEffect", jstr "readySelf")] else []) ++
        (if costs.contains .disempowerSelf then [("disempowerSelf", "true")] else []) ++
        (if costs.contains .exhaustSelf then [("exhaustSelf", "true")] else [])
      | _ => [])
    | .mulliganPick c => [("card", toString c.n)]
    | .discardPick c => [("card", toString c.n)]
    | .decide yes =>
      [("yes", if yes then "true" else "false")] ++
        (match frame with
        | some (.groupMove _ dest pay units) =>
          [("groupMoveUnits", jarr (units.map (fun u => toString u.n)))] ++ moveFields dest pay
        | some (.triggerOrder _ _ _ _ (some _)) => [("cancelTriggerFunding", "true")]
        | some (.eitherDo _ _ _ (.prim (.attachPaying ..)) (.doThen (.prim (.exhaust _)) _) _) =>
          [("equipPayment", jstr (if yes then "resources" else "exhaust"))]
        | _ => []) ++
        tokenLocationFields frame yes ++ damageOrderFields frame yes ++ damageDivisionFields frame yes ++
        deathBanishFields frame yes ++ deathSacrificeFields frame yes ++ deathOrderFields frame yes ++
        reducedPermanentFields frame yes ++
        empowerChoiceFields frame ++ effectPaymentFields state frame yes ++
        remakeSpellFields state frame yes ++ effectSpellFields state frame yes
    | .choose o =>
      [("obj", toString o.n)] ++
        (match frame with
        | some (.groupMove ..) => [("choiceContext", jstr "groupMove")]
        | some (.pickDo _ _ _ _ _ (.collectOwnPicks ..) _) => [("choiceContext", jstr "own")]
        | some (.pickDo _ _ _ _ _ (.recordBanishReplay ..) _) => [("choiceContext", jstr "banishReplay")]
        | some (.pickDo _ _ _ _ _ .addReservedLegendPicked _) => [("choiceContext", jstr "reserveLegend")]
        | some (.pickDo _ _ _ _ _ (.retainTargetSet _) _) => [("choiceContext", jstr "retain")]
        | some (.pickDo _ _ _ _ _ (.doThen (.prim (.exhaust _)) _) _) =>
          [("choiceContext", jstr "equipExhaust")]
        | some (.pickDo _ _ _ _ _ (.banishLookedForPlay _) _) => [("choiceContext", jstr "lookedDeck")]
        | some (.pickDo _ _ _ _ _ (.prim (.castInline _)) _) => [("choiceContext", jstr "trashSpell")]
        | some (.pickDo _ _ _ _ _ (.prim (.playReduced _ _ none)) _) =>
          if (state.bind (·.locate o)).any (fun | .player _ .mainDeck => true | _ => false) then
            [("choiceContext", jstr "revealedPlay")] else []
        | some (.pickDo _ _ env _ _ (.prim (.copyAttachedFrom _)) _) =>
          [("choiceContext", jstr "attachmentCopy")] ++ (match env.slots.head? with
            | some (.obj unit) => [("unit", toString unit.n)]
            | _ => [])
        | some (.pickDo _ _ env _ _ _ _) =>
          if env.revealedCards.contains o then [("choiceContext", jstr "revealedHand")] else []
        | _ => [])
    | .predictPick card recycle =>
      [("card", toString card.n), ("recycle", if recycle then "true" else "false")]
    | .nameCard card => [("cardCode", jstr card.code)]
    | .guessCardType guess => [("cardType", jstr (ctorName guess))]
    | .burnOutTarget o => [("opponent", toString o.n)]
    | .inviteTeammate guest => [("guest", toString guest.n)]
    | .pick i => [("index", toString i)]
    | _ => []
  jobj ([("actor", jstr who), ("kind", jstr kind)] ++ extra)

/-- An event as JSON. -/
def eventJson : Event → String
  | .moved o n dst =>
    jobj [("t", jstr "moved"), ("old", toString o.n), ("new", toString n.n),
      ("dst", jstr (zoneName dst))]
  | .banished p owner c =>
    jobj [("t", jstr "banished"), ("player", toString p.n), ("owner", toString owner.n),
      ("card", toString c.n)]
  | .pointsGained p n =>
    jobj [("t", jstr "points"), ("player", toString p.n), ("n", toString n)]
  | .burnedOut p => jobj [("t", jstr "burnout"), ("player", toString p.n)]
  | .burnedUnitFor p source _ idx card might =>
    jobj [("t", jstr "burned_unit"), ("player", toString p.n), ("source", toString source.n),
      ("index", toString idx), ("card", toString card.n), ("might", toString might)]
  | .discardedTypeFor p source _ idx card =>
    jobj [("t", jstr "discarded_type"), ("player", toString p.n), ("source", toString source.n),
      ("index", toString idx), ("card", toString card.n)]
  | .skipped o => jobj [("t", jstr "skipped"), ("card", toString o.n)]
  | .damaged o n => jobj [("t", jstr "damaged"), ("target", toString o.n), ("n", toString n)]
  | .healed o n => jobj [("t", jstr "healed"), ("target", toString o.n), ("n", toString n)]
  | .readied o => jobj [("t", jstr "readied"), ("target", toString o.n)]
  | .phaseStarted p ph =>
    jobj [("t", jstr "phase"), ("player", toString p.n),
      ("phase", jstr (match ph with
        | .setup => "setup" | .awaken => "awaken" | .beginning => "beginning"
        | .channel => "channel" | .draw => "draw" | .main => "main" | .ending => "ending"))]
  | .stunned o => jobj [("t", jstr "stunned"), ("target", toString o.n)]
  | .buffed o => jobj [("t", jstr "buffed"), ("target", toString o.n)]
  | .becameMighty o => jobj [("t", jstr "became_mighty"), ("unit", toString o.n)]
  | .mightReached o n => jobj [("t", jstr "might_reached"), ("unit", toString o.n),
      ("threshold", toString n)]
  | .mightReduced p o n => jobj [("t", jstr "might_reduced"), ("player", toString p.n),
      ("unit", toString o.n), ("n", toString n)]
  | .empowered p o =>
    jobj [("t", jstr "empowered"), ("player", toString p.n), ("target", toString o.n)]
  | .conquerActivated u => jobj [("t", jstr "conquer_activated"), ("unit", toString u.n)]
  | .lookedAt p c => jobj [("t", jstr "looked_at"), ("player", toString p.n), ("card", toString c.n)]
  | .namedCard p source card =>
    jobj [("t", jstr "named_card"), ("player", toString p.n), ("source", toString source.n),
      ("cardCode", jstr card.code)]
  | .chosenBySpell p t => jobj [("t", jstr "chosen_by_spell"), ("player", toString p.n), ("target", toString t.n)]
  | .chosenByAbility p t => jobj [("t", jstr "chosen_by_ability"), ("player", toString p.n), ("target", toString t.n)]
  | .killedBySpell p => jobj [("t", jstr "killed_by_spell"), ("player", toString p.n)]
  | .recycled p => jobj [("t", jstr "recycled"), ("player", toString p.n)]
  | .hiddenPlayed p => jobj [("t", jstr "hidden_played"), ("player", toString p.n)]
  | .drew p => jobj [("t", jstr "drew"), ("player", toString p.n)]
  | .drewGroup p otherCards =>
    jobj [("t", jstr "drewGroup"), ("player", toString p.n), ("otherCards", toString otherCards)]
  | .movedByEffect p u =>
    jobj [("t", jstr "moved_by_effect"), ("player", toString p.n), ("unit", toString u.n)]
  | .discarded p o _ =>
    jobj [("t", jstr "discarded"), ("player", toString p.n), ("obj", toString o.n)]
  | .exhausted o => jobj [("t", jstr "exhausted"), ("target", toString o.n)]
  | .exhaustBatch who objects beforeMove =>
    jobj [("t", jstr "exhaustBatch"), ("player", who.elim "null" (fun p => toString p.n)),
      ("objects", jarr (objects.map (fun o => toString o.n))),
      ("beforeMove", if beforeMove then "true" else "false")]
  | .standardMoved u d =>
    jobj [("t", jstr "moved_unit"), ("unit", toString u.n),
      ("dest", match d with | some bf => toString bf.n | none => "null")]
  | .controlChanged bf p =>
    jobj [("t", jstr "control"), ("battlefield", toString bf.n),
      ("player", match p with | some q => toString q.n | none => "null")]
  | .scored p bf conquer =>
    jobj [("t", jstr "scored"), ("player", toString p.n), ("battlefield", toString bf.n),
      ("conquer", if conquer then "true" else "false")]
  | .scoreDraw p bf =>
    jobj [("t", jstr "score_draw"), ("player", toString p.n), ("battlefield", toString bf.n)]
  | .recalled u => jobj [("t", jstr "recalled"), ("unit", toString u.n)]
  | .won p => jobj [("t", jstr "won"), ("player", toString p.n)]
  | .played p o => jobj [("t", jstr "played"), ("player", toString p.n), ("obj", toString o.n)]
  | .spellResolved p o =>
    jobj [("t", jstr "spellResolved"), ("player", toString p.n), ("obj", toString o.n)]
  | .died o p => jobj [("t", jstr "died"), ("obj", toString o.n), ("player", toString p.n)]
  | .combatStarted bf att =>
    jobj [("t", jstr "combat"), ("battlefield", toString bf.n), ("attacker", toString att.n)]
  | .combatJoined bf att units =>
    jobj [("t", jstr "combat_joined"), ("battlefield", toString bf.n), ("attacker", toString att.n),
      ("units", jarr (units.map (fun u => toString u.n)))]
  | .combatEnded bf units =>
    jobj [("t", jstr "combat_ended"), ("battlefield", toString bf.n),
      ("units", jarr (units.map (fun u => toString u.n)))]
  | .attached g u =>
    jobj [("t", jstr "attached"), ("gear", toString g.n), ("unit", toString u.n)]
  | .buffSpent p => jobj [("t", jstr "buff_spent"), ("player", toString p.n)]
  | .tokenPlayed p t =>
    jobj [("t", jstr "token_played"), ("player", toString p.n), ("token", toString t.n)]
  | .revealed p c =>
    jobj [("t", jstr "revealed"), ("player", toString p.n), ("card", toString c.n)]
  | .handRevealed p ids =>
    jobj [("t", jstr "hand_revealed"), ("player", toString p.n),
      ("cards", jarr (ids.map (fun id => toString id.n)))]
  | .combatWon bf w =>
    jobj [("t", jstr "combat_won"), ("battlefield", toString bf.n), ("winner", toString w.n)]
  | .activated p src idx baseEnergy =>
    jobj ([("t", jstr "activated"), ("player", toString p.n), ("source", toString src.n),
      ("index", toString idx)] ++ baseEnergy.toList.map (fun n => ("baseEnergy", toString n)))

/-- All the zones to show, with the player count. -/
def shownZones (n : Nat) : List Zone :=
  (allPlayers n).flatMap (fun p => ZoneKind.all.map (fun k => Zone.player p k)) ++
    [.battlefieldZone, .chain]

/-- The identifiers of all objects in the zones. -/
def shownIds (s : GameState) : List ObjId :=
  (shownZones s.playerCount).flatMap (fun z => s.zone z)

/-- A new object as JSON: its card, its owner, and its Rune domain. -/
def objJson (s : GameState) (id : ObjId) : String :=
  match s.obj? id with
  | some o =>
    let card := match o.kind with
      | .card _ c => c.code
      | .token c => c.code
      | .chainAbility c _ _ => c.code
    let ability : List (String × String) := match o.kind with
      | .chainAbility _ idx src => [("source", toString src.n), ("ability", toString idx)]
      | _ => []
    jobj ([("card", jstr card), ("owner", toString o.owner.n),
      ("rune", match o.runeDomain with | some d => jstr (ctorName d) | none => "null")] ++ ability)
  | none => "null"

/-- The Rune Pool of a player as JSON. -/
def poolJson (p : RunePool) : String :=
  jobj [("energy", toString p.energy), ("unitEnergy", toString p.unitEnergy),
    ("fury", toString p.fury), ("calm", toString p.calm),
    ("mind", toString p.mind), ("body", toString p.body), ("chaos", toString p.chaos),
    ("order", toString p.order), ("any", toString p.any)]

/-- The state as JSON. `seen` are the identifiers already sent: only new objects are described. -/
def stateJson (s : GameState) (seen : Std.HashSet Nat) : String × Std.HashSet Nat :=
  let ids := shownIds s
  let fresh := ids.filter (fun id => !seen.contains id.n)
  let seen' := fresh.foldl (fun acc id => acc.insert id.n) seen
  let zones := (shownZones s.playerCount).filterMap fun z =>
    match s.zone z with
    | [] => none
    | l => some (zoneName z, jarr (l.map (fun id => toString id.n)))
  let exhausted := ids.filter (fun id => (s.obj? id).any (·.exhausted))
  let damaged := ids.filterMap (fun id =>
    match s.obj? id with
    | some o => if 0 < o.damage then some (jarr [toString id.n, toString o.damage]) else none
    | none => none)
  let boosted := ids.filterMap (fun id =>
    match s.obj? id with
    | some _ =>
      let d : Int := match s.mightNow id, (s.cardDef? id).bind (·.might) with
        | some now, some printed => now - printed
        | _, _ => 0
      if d != 0 then some (jarr [toString id.n, toString d]) else none
    | none => none)
  let stunned := ids.filter (fun id => (s.obj? id).any (·.stunned))
  let attached := ids.filterMap (fun id =>
    match (s.obj? id).bind (·.attached) with
    | some u => some (jarr [toString id.n, toString u.n])
    | none => none)
  let named := s.inPlay.filterMap (fun id =>
    ((s.obj? id).bind (·.namedCard)).map (fun card => (toString id.n, jstr card.code)))
  let copies := s.inPlay.filterMap (fun id => do
    let o ← s.obj? id
    let copy ← s.attachmentCopyOf id o
    return (toString id.n, jstr copy.card.code))
  let players := allPlayers s.playerCount
  let bfs := s.battlefields.map (fun b =>
    jobj [("id", toString b.n),
      ("control", match s.controlOf b with | some p => toString p.n | none => "null"),
      ("contested", match (s.obj? b).bind (·.contested) with
        | some p => toString p.n | none => "null")])
  let locs := (s.zone .battlefieldZone).filterMap (fun u =>
    match (s.obj? u).bind (·.loc) with
    | some b => some (jarr [toString u.n, toString b.n])
    | none => none)
  let clock := match s.clock with
    | some (.elimination deadline _) => [("eliminationDeadline", toString deadline)]
    | _ => []
  let json := jobj ([
    ("turn", toString s.turn), ("phase", jstr (ctorName s.phase)),
    ("active", match s.active with | some p => toString p.n | none => "null"),
    ("pending", match s.pending with | f :: _ => jstr (ctorName f) | [] => "null"),
    ("result", match s.result with
      | some (.won w) => jobj [("won", jarr (w.map (fun p => toString p.n)))]
      | some .draw => jstr "draw"
      | none => "null"),
    ("points", jarr (players.map (fun p => toString (s.pointsOf p)))),
    ("pools", jarr (players.map (fun p => poolJson (s.poolOf p)))),
    ("zones", jobj zones),
    ("battlefields", jarr bfs), ("at", jarr locs),
    ("new", jobj (fresh.map (fun id => (toString id.n, objJson s id)))),
    ("exhausted", jarr (exhausted.map (fun id => toString id.n))),
    ("damaged", jarr damaged), ("boosted", jarr boosted),
    ("attached", jarr attached), ("namedCards", jobj named), ("copies", jobj copies),
    ("stunned", jarr (stunned.map (fun id => toString id.n)))] ++ clock)
  (json, seen')

/-- One step of the trace: the answer given (if any), its events, and the state after it. -/
def stepJson (i : Nat) (a : Option Action) (es : List Event) (s : GameState)
    (seen : Std.HashSet Nat) (frame : Option Frame := none) : String × Std.HashSet Nat :=
  let (st, seen') := stateJson s seen
  (jobj [("i", toString i),
    ("action", match a with | some a => actionJson a frame (some s) es | none => "null"),
    ("events", jarr (es.map eventJson)), ("state", st)], seen')

/-- The parameter of a keyword as JSON. -/
def kwArgJson : KeywordArg → String
  | .none => "null"
  | .amount n => toString n
  | .cost k => costJson k
  | .costOrExhaustUnit k => jobj [("resources", costJson k), ("orExhaustFriendlyUnit", "true")]
  | .object s => jstr s
  | .equalShield => jstr "Shield"

/-- The Lean definition of what a card does, as text: abilities, effect of a Spell, grants. -/
def irText (c : CardDef) : String :=
  let part (name : String) (f : Std.Format) : String := name ++ ":\n" ++ f.pretty 90
  let l : List String :=
    (if c.abilities.isEmpty then [] else [part "abilities" (repr c.abilities)]) ++
    (match c.spellEffect with | some e => [part "spellEffect" (repr e)] | none => []) ++
    (if c.grants.isEmpty then [] else [part "grants" (repr c.grants)]) ++
    (match c.additionalCost with | some k => [part "additionalCost" (repr k)] | none => [])
  ("\n".intercalate l).replace "Riftbound." ""

/-- A card of the database as JSON: what the printed card shows, and the Lean definition of what it
does (for the details the viewer shows on a right click). -/
def cardJson (c : CardDef) : String :=
  jobj ([("name", jstr c.name), ("types", jarr (c.types.map (fun t => jstr (ctorName t)))),
    ("domains", jarr (c.domains.map (fun d => jstr (ctorName d)))),
    ("cost", match c.cost with | some k => toString k.energy | none => "null"),
    ("might", match c.might with | some m => toString m | none => "null"),
    ("subtitle", match c.subtitle with | some s => jstr s | none => "null"),
    ("supertypes", jarr (c.supertypes.map (fun t => jstr (ctorName t)))),
    ("tags", jarr (c.tags.map (fun t => jstr t.name))),
    ("costFull", match c.cost with | some k => costJson k | none => "null"),
    ("keywords", jarr (c.keywords.map (fun k =>
      jobj [("k", jstr (ctorName k.keyword)), ("arg", kwArgJson k.arg)]))),
    ("mightBonus", match c.mightBonus with | some m => toString m | none => "null"),
    ("ir", jstr (irText c))] ++
    c.additionalCost.toList.map (fun cost => ("optionalCost", costJson cost)) ++
    c.spellObjectCost.toList.map (fun cost => ("spellObjectCost", jstr (ctorName cost.1))) ++
    (if c.discardToPlay then [("discardToPlay", "true")] else []))

/-- The answer of the demo player in the Main Phase: play a card if one can be paid for, otherwise
send a Unit to a Battlefield, exhaust the Runes that are ready, recycle one Rune on even turns
when no Power is in the Pool, and pass. Everything else is answered as `autoAnswer` does. Only a
legal answer is chosen: the list of `legalActions` is searched. -/
def demoAnswer (r : Rng) (s : GameState) : Option (Action × Rng) :=
  match s.pending with
  | .priority p :: _ =>
    let legal := legalActions s
    let isAb (ab : RuneAbility) (a : Action) : Bool :=
      match a.kind with | .runeAbility _ ab' => ab' == ab | _ => false
    let isPlay (a : Action) : Bool :=
      match a.kind with | .playCard _ _ _ _ _ _ => true | _ => false
    let isGo (a : Action) : Bool :=
      match a.kind with | .standardMove _ (.battlefield _) _ => true | _ => false
    let isUse (a : Action) : Bool :=
      match a.kind with | .activate .. => true | _ => false
    let isMana (a : Action) : Bool :=
      match a.kind with | .manaAbility .. => true | _ => false
    match legal.find? isMana with
    | some a => some (a, r)
    | none =>
    -- exhaust the Runes that are ready first, so that the Pool can pay an additional cost; keep one
    -- ready to answer with a Reaction on the other player's turn
    let holdsReaction := (s.zone (.player p .hand)).any (reactSpell s)
    let exhausts := legal.filter (isAb .exhaust)
    match (if holdsReaction && exhausts.length ≤ 1 then none else exhausts.head?) with
    | some a => some (a, r)
    | none =>
    match legal.find? isPlay with
    | some a0 =>
      -- the same card and targets: pay the additional cost when there is one
      let payOf (a : Action) : Nat :=
        match a.kind with | .playCard _ pay _ _ _ _ => pay.energy + pay.power.length | _ => 0
      let same (a : Action) : Bool :=
        match a.kind, a0.kind with
        | .playCard c _ _ _ discard _, .playCard c0 _ _ _ discard0 _ =>
          c == c0 && a.targetsOf == a0.targetsOf && discard == discard0
        | _, _ => false
      let extrasOf (a : Action) : Nat :=
        match a.kind with
        | .playCard _ _ _ _ _ pick => (pick.permanentCosts.map List.length).getD 0
        | _ => 0
      let best := (legal.filter same).foldl (fun acc a =>
        if payOf a > payOf acc || (payOf a == payOf acc && extrasOf a > extrasOf acc) then a else acc) a0
      some (best, r)
    | none =>
    match legal.find? isUse with
    | some a => some (a, r)
    | none =>
    match legal.find? isGo with
    | some a => some (a, r)
    | none =>
      if s.turn % 2 == 0 && (s.poolOf p).fury == 0 then
        match legal.find? (isAb .recycle) with
        | some a => some (a, r)
        | none => some (⟨.player p, .pass⟩, r)
      else some (⟨.player p, .pass⟩, r)
  | .chainPass p _ :: _ =>
    -- answer an item of the opponent: cast a Reaction if one can be paid for, or exhaust a Rune
    -- when one is in the hand
    let legal := legalActions s
    let isPlay (a : Action) : Bool :=
      match a.kind with | .playCard _ _ _ _ _ _ => true | _ => false
    let isExhaust (a : Action) : Bool :=
      match a.kind with | .runeAbility _ .exhaust => true | _ => false
    let holdsReaction := (s.zone (.player p .hand)).any (reactSpell s)
    if s.active == some p then some (⟨.player p, .pass⟩, r)
    else
      match legal.find? isPlay with
      | some a => some (a, r)
      | none =>
        if holdsReaction && (s.poolOf p).energy == 0 then
          match legal.find? isExhaust with
          | some a => some (a, r)
          | none => some (⟨.player p, .pass⟩, r)
        else some (⟨.player p, .pass⟩, r)
  | _ => autoAnswer r s

/-- Play with `demoAnswer` until the turn player passes in turn `turns`, or `n` answers. The steps
of the trace come back in reverse order. -/
def playTrace (turns : Nat) (cap : Option Nat := none) (judge : Bool := false) :
    Nat → Nat → Rng → GameState → Std.HashSet Nat → List String →
      Except RuleError (List String)
  | 0, _, _, _, _, acc => .ok acc
  | n + 1, i, r, s, seen, acc =>
    match (if (cap.any (· ≤ s.turn)) && s.clock.isNone && s.active.isSome && s.result.isNone then
        some ((if judge then ⟨.judge, .declareDraw⟩ else ⟨.clock, .timeCalled⟩), r)
      else demoAnswer r s) with
    | none => .ok acc
    | some (a, r') =>
      match step 100 s a with
      | .error e => .error e
      | .ok (s', es) =>
        let (j, seen') := stepJson i (some a) es s' seen s.pending.head?
        let atPriority := match s.pending with | .priority _ :: _ => true | _ => false
        if a.kind == .pass && atPriority && turns ≤ s.turn then .ok (j :: acc)
        else playTrace turns cap judge n (i + 1) r' s' seen' (j :: acc)

/-- The whole trace of a demo game of `turns` turns from `seed`, as JSON. With `timed`, the game is
played under the Tournament Rules, and the clock calls time when `turns` turns have begun: the
game goes on to its end (TR 408.2). With `judge`, the judge declares a draw then instead
(TR 505.6). With `limited`, the game is set up from Sealed decks with no Legend and no Chosen
Champion, so that each player draws 1 more in their first turn (TR 602.4.a.5.b). -/
def demoTrace (seed turns : Nat) (timed : Bool := false) (judge : Bool := false)
    (limited : Bool := false) : Except String String :=
  match (if limited then
      GameState.initialLimited demoDB { legalSets := [], banned := [] }
        { ruleSet := .tournament .sealed, mode := Mode.duel } [demoLimitedDeck, demoLimitedDeck]
    else
      GameState.initial demoDB
        (if timed || judge then
          { ruleSet := .tournament .constructed, mode := Mode.duel, formatLegality := some demoEnv }
        else demoConfig)
        [demoDeck, demoDeck]) with
  | none => .error "the demo game cannot be set up"
  | some s0 =>
    let (j0, seen) := stepJson 0 none [] s0 {}
    match playTrace (if timed || judge then 100000 else turns)
        (if timed || judge then some turns else none) judge 100000 1 (Rng.ofSeed seed) s0 seen
        [j0] with
    | .error e => .error s!"the engine refused an answer: {repr e}"
    | .ok acc =>
      .ok (jobj [("seed", toString seed), ("players", toString s0.playerCount),
        ("cards", jobj (demoCards.map (fun c => (c.id.code, cardJson c)))),
        ("steps", jarr acc.reverse)])

end RiftboundDriver

end
