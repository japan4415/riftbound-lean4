module

public import Riftbound.Rules.Play
public import Riftbound.Rules.Remove
public import Riftbound.Rules.Owner
public import Riftbound.Rules.Actions.BurnOut
public import Riftbound.Rules.Actions.Draw
public import Riftbound.Tournament.DeckLegality

/-!
# Running an effect

The interpreter of the effect IR, one step at a time (design.md §6.1, §7.1). A `run` frame holds
the effects still to do; `runEffect` looks at the first and says which frames replace the `run`
frame. Only a few instructions have a meaning yet: doing nothing, a sequence, a bound variable,
and drawing. An instruction that cannot be done is skipped with an event, never an error (design.md
§7.1), so that the interpreter is total.
-/

@[expose] public section

namespace Riftbound

/-- The effects of the first list, then those of the second. -/
def EffectList.append : EffectList → EffectList → EffectList
  | .nil, l => l
  | .cons e rest, l => .cons e (rest.append l)

/-- `n` copies of an effect. -/
def EffectList.replicate : Nat → Effect → EffectList
  | 0, _ => .nil
  | n + 1, e => .cons e (EffectList.replicate n e)

namespace GameState

/-- The player who gets priority after `p`: the next one in the turn order (CR 311). -/
def nextPlayer (s : GameState) (p : PlayerId) : PlayerId :=
  match s.turnOrder.idxOf? p with
  | some i => s.turnOrder.getD ((i + 1) % s.turnOrder.length) p
  | none => p

/-- Pass priority or focus to the next continuing seat (CR 652.5.b, 652.5.c). -/
def nextParticipant (s : GameState) (p : PlayerId) : PlayerId :=
  if s.departures.seats.isEmpty then s.nextPlayer p else
    ((seatOrderAfter s.turnOrder p).find? s.participates <|> s.participatingOrder.head?).getD p

/-- The seat that starts the next round of passes after a Chain item has resolved. -/
def chainPrioritySeat (s : GameState) : PlayerId :=
  let turnPlayer := s.active.getD ⟨0⟩
  if s.departures.seats.isEmpty || s.participates turnPlayer then turnPlayer
  else s.nextParticipant turnPlayer

end GameState

/-- Put each object of the list through `g`, one after the other: the last state, and all the
events. -/
def applyEach {α : Type} (g : GameState → α → GameState × List Event) :
    GameState → List α → GameState × List Event
  | s, [] => (s, [])
  | s, id :: ids =>
    let r := g s id
    let r2 := applyEach g r.1 ids
    (r2.1, r.2 ++ r2.2)

/-- Putting each object through changes that are safe is a safe change. -/
theorem applyEach_safe {α : Type} {g : GameState → α → GameState × List Event}
    (hg : ∀ s id, Safe s (g s id).1) : ∀ (ids : List α) (s : GameState),
      Safe s (applyEach g s ids).1
  | [], s => Safe.refl s
  | id :: ids, s => (hg s id).trans (applyEach_safe hg ids (g s id).1)

/-- The Chosen Champion of the player: a Unit of the Champion the Legend of the player is about
(they share a tag). The card data does not tell Champions from other Units, nor the Chosen
Champion from its copies. -/
def GameState.chosenOf (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  let tags := (s.zone (.player p .legendZone)).flatMap (fun l =>
    ((s.cardDef? l).map (·.tags)).getD [])
  (s.cardDef? id).any (fun d =>
    d.hasType .unit && d.tags.any (fun t => tags.contains t))

/-- The player returns their Chosen Champion from their Trash to their Champion Zone, if the
Champion Zone is empty. -/
def returnChampion (p : PlayerId) (s : GameState) : GameState × List Event :=
  if (s.zone (.player p .championZone)).isEmpty then
    match (s.zone (.player p .trash)).find? (fun u => s.chosenOf p u) with
    | some id => sendObj .championZone s id
    | none => (s, [])
  else (s, [])

/-- Returning the Chosen Champion is a safe change. -/
theorem returnChampion_safe (p : PlayerId) (s : GameState) : Safe s (returnChampion p s).1 := by
  unfold returnChampion
  split
  · split
    · exact sendObj_safe _ _ _
    · exact Safe.refl s
  · exact Safe.refl s

/-- Heal `n` damage from an object (CR 419). -/
def healOne (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some _ => (s.modObj id (fun o => { o with damage := o.damage - n }), [Event.healed id n])
  | none => (s, [])

/-- Healing is a safe change. -/
theorem healOne_safe (n : Nat) (s : GameState) (id : ObjId) : Safe s (healOne n s id).1 := by
  unfold healOne
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- A spell or an ability cannot ready the Units and Gear of the opponents of a player who has a
passive ability that says so. -/
def readyBlocked (s : GameState) (id : ObjId) : Bool :=
  ((s.obj? id).any (fun o => s.oppHas o.controller .noReadyOfOpps) &&
    (s.cardDef? id).any (fun d => d.hasType .unit || d.hasType .gear)) ||
  (s.obj? id).any (·.cantReady) ||
  (s.phase == .awaken && (s.cardDef? id).any (·.hasType .unit) && s.anyActive .skipUnitAwaken)

/-- A spell or an ability readies an object, unless it cannot. -/
def readyEffect (s : GameState) (id : ObjId) : GameState × List Event :=
  if readyBlocked s id then (s, []) else setExhausted false s id

/-- Readying by an effect is a safe change. -/
theorem readyEffect_safe (s : GameState) (id : ObjId) : Safe s (readyEffect s id).1 := by
  unfold readyEffect
  split
  · exact Safe.refl s
  · exact setExhausted_safe false s id

/-- Put each object that the selector stands for through `g`. `none` if the selector cannot be
answered yet. -/
def onSelected (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (g : GameState → ObjId → GameState × List Event) : Option (GameState × List Event) :=
  (sel.eval s p src env).map (fun ids => applyEach g s ids)

/-- Changes of the selected objects that are safe are a safe change. -/
theorem onSelected_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {sel : Selector}
    {g : GameState → ObjId → GameState × List Event} (hg : ∀ s id, Safe s (g s id).1)
    {r : GameState × List Event} (h : onSelected s p src env sel g = some r) : Safe s r.1 := by
  unfold onSelected at h
  cases hs : sel.eval s p src env with
  | none => simp [hs] at h
  | some ids =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst h
    exact applyEach_safe hg ids s

/-- Adding an object that is not a physical card is a safe change. -/
theorem safe_addObject {s s' : GameState} {o : Object} {z : Zone} {pos : Pos} {id : ObjId}
    (hk : o.kind.phys? = none) (h : addObject s o z pos = some (s', id)) : Safe s s' :=
  ⟨fun hwf => addObject_wf hwf h, fun hwf => addObject_physIds hwf h hk,
    fun hwf hown => addObject_ownerOk hwf hown h, addObject_sameMeta h⟩

/-- The identifier of the card of a token the model defines itself (CR 179). -/
def tokenId (name : String) : CardId := ⟨"TKN-" ++ name⟩

/-- Cards that can be named for this type, whether or not a copy exists in the game (CR 759-762). -/
def GameState.nameableCards (s : GameState) (kind : CardType) : List CardId :=
  (s.cards.cards.filter (fun d =>
    d.hasType kind && !d.isTokenCard &&
      (match s.config.ruleSet.tournamentFormat, s.config.formatLegality with
        | some .constructed, some env => decide (CardLegal env d)
        | some _, some env => decide (NotBanned env d)
        | _, _ => true))).map (·.id)

/-- The card of the token with the name: one the model defines, or one of the printed tokens. -/
def GameState.tokenCard (s : GameState) (name : String) : Option CardDef :=
  match s.cards.find? (tokenId name) with
  | some c => some c
  | none => s.cards.cards.find? (fun c => c.isTokenCard && c.name == name)

/-- Add an object that is not a physical card to a zone; nothing if it cannot be added. -/
def addTok (s : GameState) (o : Object) (z : Zone) : GameState :=
  match addObject s o z with
  | some r => r.1
  | none => s

/-- Adding a token is a safe change. -/
theorem addTok_safe (s : GameState) (o : Object) (z : Zone) (hk : o.kind.phys? = none) :
    Safe s (addTok s o z) := by
  unfold addTok
  split
  · rename_i r hr
    exact safe_addObject hk hr
  · exact Safe.refl s

/-- Make one token for the player: on their Base, or at the Battlefield `dest` (CR 183). -/
def createOne (card : CardId) (p : PlayerId) (dest : Option ObjId) (ready : Bool)
    (s : GameState) : GameState :=
  let o : Object :=
    { kind := .token card, owner := p, controller := p, exhausted := !ready,
      timestamp := ⟨0⟩, loc := dest }
  match dest with
  | some _ => addTok s o .battlefieldZone
  | none => addTok s o (.player p .base)

/-- Making a token is a safe change. -/
theorem createOne_safe (card : CardId) (p : PlayerId) (dest : Option ObjId) (ready : Bool)
    (s : GameState) : Safe s (createOne card p dest ready s) := by
  unfold createOne
  cases dest <;> exact addTok_safe _ _ _ rfl

/-- Make `n` tokens. -/
def createN (card : CardId) (p : PlayerId) (dest : Option ObjId) (ready : Bool) :
    Nat → GameState → GameState
  | 0, s => s
  | n + 1, s => createN card p dest ready n (createOne card p dest ready s)

/-- Making tokens is a safe change. -/
theorem createN_safe (card : CardId) (p : PlayerId) (dest : Option ObjId) (ready : Bool) :
    ∀ (n : Nat) (s : GameState), Safe s (createN card p dest ready n s)
  | 0, s => Safe.refl s
  | n + 1, s => (createOne_safe card p dest ready s).trans (createN_safe card p dest ready n _)

/-- Add a lasting change of Might to an object (CR 475-478). -/
def addMightMod (m : MightMod) (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with mightMods := o.mightMods ++ [m] }), [])

/-- Adding a change of Might is a safe change. -/
theorem addMightMod_safe (m : MightMod) (s : GameState) (id : ObjId) :
    Safe s (addMightMod m s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- Replace a stun, a Might reduction or a return to hand on a chosen Unit with a
Might bonus if its active abilities say so (CR 370). -/
def replaceChosenHarm (env : Env) (apply : GameState → ObjId → GameState × List Event)
    (s : GameState) (id : ObjId) : GameState × List Event :=
  if env.targetObjs.contains id && s.inPlay.contains id then
    match (s.activeMods id).findSome? (fun
      | .chosenHarmToMight n => some n
      | _ => none) with
    | some n => addMightMod ⟨(n : Int), .turn⟩ s id
    | none => apply s id
  else apply s id

/-- Replacing chosen harm preserves safety when the original instruction does. -/
theorem replaceChosenHarm_safe (env : Env) {apply : GameState → ObjId → GameState × List Event}
    (h : ∀ s id, Safe s (apply s id).1) (s : GameState) (id : ObjId) :
    Safe s (replaceChosenHarm env apply s id).1 := by
  unfold replaceChosenHarm
  split
  · split
    · exact addMightMod_safe _ s id
    · exact h s id
  · exact h s id

/-- An already stunned object produces no new stun event or replacement (CR 424, 370). -/
def stunObj (s : GameState) (id : ObjId) (env : Env := {}) : GameState × List Event :=
  if (s.obj? id).any (! ·.stunned) then
    replaceChosenHarm env (fun t target =>
      (t.modObj target (fun o => { o with stunned := true }), [Event.stunned target])) s id
  else (s, [])

/-- Stunning is a safe change. -/
theorem stunObj_safe (s : GameState) (id : ObjId) (env : Env := {}) :
    Safe s (stunObj s id env).1 := by
  unfold stunObj
  split
  · exact replaceChosenHarm_safe env (fun t target =>
      Safe.modObj t target (f := fun o => { o with stunned := true })
        (fun _ => rfl) (fun _ => rfl)) s id
  · exact Safe.refl s

/-- Buff an object: it gets a +1 Might buff if it has none (CR 701). -/
def buffObj (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    -- a Unit that can have any number of buffs gets one more
    if o.buffed && (s.activeMods id).contains .anyBuffs then
      (s.modObj id (fun o => { o with extraBuffs := o.extraBuffs + 1 }), [Event.buffed id])
    else
      (s.modObj id (fun o => { o with buffed := true }),
        if o.buffed then [] else [Event.buffed id])
  | none => (s, [])

/-- Buffing is a safe change. -/
theorem buffObj_safe (s : GameState) (id : ObjId) : Safe s (buffObj s id).1 := by
  unfold buffObj
  split
  · split <;> exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- Spend the buff of an object: it loses it (CR 704). -/
def unbuffObj (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o =>
    if 0 < o.extraBuffs then { o with extraBuffs := o.extraBuffs - 1 }
    else { o with buffed := false }),
    match s.obj? id with
    | some o => if o.buffed || 0 < o.extraBuffs then [Event.buffSpent o.controller] else []
    | none => [])

/-- Spending a buff is a safe change. -/
theorem unbuffObj_safe (s : GameState) (id : ObjId) : Safe s (unbuffObj s id).1 :=
  Safe.modObj s id (fun _ => by split <;> rfl) (fun _ => by split <;> rfl)

/-- The player gains XP and the turn records that gain (CR 730.1). -/
def gainXPOf (n : Nat) (s : GameState) (p : PlayerId) : GameState :=
  if 0 < n then (s.setXP p (s.xpOf p + n)).addTurnFx p .gainedXP else s

/-- Gaining XP is a safe change. -/
theorem gainXPOf_safe (n : Nat) (s : GameState) (p : PlayerId) : Safe s (gainXPOf n s p) := by
  unfold gainXPOf
  split
  · exact (Safe.setXP s p _).trans (addTurnFx_safe _ p _)
  · exact Safe.refl s

/-- The players gain XP, one after the other. -/
def gainXPAll (n : Nat) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, p :: ps => gainXPAll n (gainXPOf n s p) ps

/-- Gaining XP is a safe change, for any players. -/
theorem gainXPAll_safe (n : Nat) : ∀ (ps : List PlayerId) (s : GameState),
    Safe s (gainXPAll n s ps)
  | [], s => Safe.refl s
  | p :: ps, s => (gainXPOf_safe n s p).trans (gainXPAll_safe n ps _)

/-- The players spend XP, one after the other. -/
def spendXPAll (n : Nat) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, p :: ps => spendXPAll n (s.spendXP p n) ps

/-- Spending XP is a safe change, for any players. -/
theorem spendXPAll_safe (n : Nat) : ∀ (ps : List PlayerId) (s : GameState),
    Safe s (spendXPAll n s ps)
  | [], s => Safe.refl s
  | p :: ps, s => (Safe.spendXP s p n).trans (spendXPAll_safe n ps _)

/-- The player recycles the top card of their Main Deck: it goes to the bottom (CR 417). -/
def recycleTopOf (q : PlayerId) (s : GameState) : GameState :=
  match s.zone (.player q .mainDeck) with
  | [] => s
  | x :: rest =>
    if (Zone.player q .mainDeck).Valid s.playerCount then
      s.reorder (.player q .mainDeck) (rest ++ [x])
    else s

/-- Recycling the top card is a safe change. -/
theorem recycleTopOf_safe (q : PlayerId) (s : GameState) : Safe s (recycleTopOf q s) := by
  unfold recycleTopOf
  split
  · exact Safe.refl s
  · rename_i x rest hz
    split
    · rename_i hv
      have hp : (rest ++ [x]).Perm (s.zone (.player q .mainDeck)) := by
        rw [hz]; exact List.perm_append_singleton x rest
      exact ⟨fun hwf => GameState.wf_reorder hwf hv hp, fun _ => GameState.physIds_reorder hv hp,
        fun _ hown => GameState.ownerOk_reorder hown hp, rfl⟩
    · exact Safe.refl s

/-- The player swaps the top two cards of their Main Deck. -/
def swapTopOf (q : PlayerId) (s : GameState) : GameState :=
  match s.zone (.player q .mainDeck) with
  | a :: b :: rest =>
    if (Zone.player q .mainDeck).Valid s.playerCount then
      s.reorder (.player q .mainDeck) (b :: a :: rest)
    else s
  | _ => s

/-- Swapping the top two cards is a safe change. -/
theorem swapTopOf_safe (q : PlayerId) (s : GameState) : Safe s (swapTopOf q s) := by
  unfold swapTopOf
  split
  · rename_i a b rest hz
    split
    · rename_i hv
      have hp : (b :: a :: rest).Perm (s.zone (.player q .mainDeck)) := by
        rw [hz]; exact List.Perm.swap a b rest
      exact ⟨fun hwf => GameState.wf_reorder hwf hv hp, fun _ => GameState.physIds_reorder hv hp,
        fun _ hown => GameState.ownerOk_reorder hown hp, rfl⟩
    · exact Safe.refl s
  · exact Safe.refl s

/-- The players swap the top two cards of their Main Deck, one after the other. -/
def swapTopAll : GameState → List PlayerId → GameState
  | s, [] => s
  | s, q :: qs => swapTopAll (swapTopOf q s) qs

/-- Swapping the top cards is a safe change. -/
theorem swapTopAll_safe : ∀ (qs : List PlayerId) (s : GameState), Safe s (swapTopAll s qs)
  | [], s => Safe.refl s
  | q :: qs, s => (swapTopOf_safe q s).trans (swapTopAll_safe qs _)

/-- The players recycle the top card of their Main Deck, one after the other. -/
def recycleTopAll : GameState → List PlayerId → GameState
  | s, [] => s
  | s, q :: qs => recycleTopAll (recycleTopOf q s) qs

/-- Recycling the top cards is a safe change. -/
theorem recycleTopAll_safe : ∀ (qs : List PlayerId) (s : GameState), Safe s (recycleTopAll s qs)
  | [], s => Safe.refl s
  | q :: qs, s => (recycleTopOf_safe q s).trans (recycleTopAll_safe qs _)

/-- The deck a card is recycled to: a Rune goes to the Rune Deck, any other card to the Main Deck
(CR 417). -/
def recycleKind (s : GameState) (id : ObjId) : ZoneKind :=
  if (s.cardDef? id).any (·.hasType .rune) then .runeDeck else .mainDeck

/-- Recycle a card: it goes to the bottom of its owner's deck (CR 417). -/
def recycleOne (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    let z := Zone.player o.owner (recycleKind s id)
    -- a card of the deck goes to its bottom, in the same zone
    if (s.zone z).contains id ∧ z.Valid s.playerCount then
      (s.reorder z (((s.zone z).erase id) ++ [id]), [])
    else
    match moveObj s id z .bottom with
    | some r => (r.1, [Event.moved id r.2 z])
    | none => (s, [])
  | none => (s, [])

/-- Recycling a card is a safe change. -/
theorem recycleOne_safe (s : GameState) (id : ObjId) : Safe s (recycleOne s id).1 := by
  unfold recycleOne
  cases ho : s.obj? id with
  | none => simpa [ho] using Safe.refl s
  | some o =>
    by_cases hc : ((s.zone (Zone.player o.owner (recycleKind s id))).contains id = true ∧
        (Zone.player o.owner (recycleKind s id)).Valid s.playerCount)
    · simp only [hc, and_self, ite_true]
      have hmem : id ∈ s.zone (Zone.player o.owner (recycleKind s id)) :=
        List.contains_iff_mem.mp hc.1
      have hp : (((s.zone (Zone.player o.owner (recycleKind s id))).erase id) ++ [id]).Perm
          (s.zone (Zone.player o.owner (recycleKind s id))) :=
        (List.perm_append_singleton id _).trans (List.perm_cons_erase hmem).symm
      exact ⟨fun hwf => GameState.wf_reorder hwf hc.2 hp,
        fun _ => GameState.physIds_reorder hc.2 hp,
        fun _ hown => GameState.ownerOk_reorder hown hp, rfl⟩
    · simp only [hc, ite_false]
      cases hm : moveObj s id (Zone.player o.owner (recycleKind s id)) .bottom with
      | none => simpa [hm] using Safe.refl s
      | some r => simpa [hm] using Safe.moveObj hm

/-- The note on a card hidden at the Battlefield on the turn (CR 811). -/
def hiddenOf (bf : ObjId) (t : Nat) (x : Object) : Object :=
  { x with hiddenAt := some bf, hiddenTurn := some t }

/-- Hide a card face down at the Battlefield (CR 811): it goes to its owner's hidden cards, and is
noted with the Battlefield and the turn. -/
def hideObj (bf : ObjId) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    -- only a card that is in the hand of its owner can be hidden
    if !(s.zone (.player o.owner .hand)).contains id then (s, []) else
    match moveObj s id (.player o.owner .hidden) with
    | some r =>
      (r.1.modObj r.2 (hiddenOf bf s.turn), [Event.moved id r.2 (.player o.owner .hidden)])
    | none => (s, [])
  | none => (s, [])

/-- Hiding a card is a safe change. -/
theorem hideObj_safe (bf : ObjId) (s : GameState) (id : ObjId) : Safe s (hideObj bf s id).1 := by
  unfold hideObj
  split
  · split
    · exact Safe.refl s
    · split
      · rename_i r hr
        have h1 : Safe r.1 (r.1.modObj r.2 (hiddenOf bf s.turn)) :=
          Safe.modObj r.1 r.2 (fun _ => rfl) (fun _ => rfl)
        exact (Safe.moveObj hr).trans h1
      · exact Safe.refl s
  · exact Safe.refl s

/-- The object played anew: not at a Battlefield, with the note of the play. -/
def Object.freshPlay (mk : PlayMark) (o : Object) : Object :=
  { Object.withPlay [] mk o with loc := none }

/-- What a card played anew has not: damage, a buff, a stun, lasting changes. -/
def Object.cleared (o : Object) : Object :=
  { o with damage := 0, buffed := false, extraBuffs := 0, stunned := false, mightMods := [],
           tempKws := [] }

/-- A card enters the Base as a new object, played. -/
def enterBase (p : PlayerId) (d : CardDef) (mk : PlayMark) (rdy : Bool) (s : GameState)
    (id : ObjId) : GameState :=
  -- the player who plays it controls it, even if the card is another player's (Blind Fury)
  let s2 := s.modObj id (fun o =>
    { (Object.freshPlay mk o).cleared with controller := p, buffed := mk.buff })
  if (d.hasType .unit && !rdy) || d.entersExhausted then (setExhausted true s2 id).1 else s2

/-- Entering the Base is a safe change. -/
theorem enterBase_safe (p : PlayerId) (d : CardDef) (mk : PlayMark) (rdy : Bool) (s : GameState)
    (id : ObjId) : Safe s (enterBase p d mk rdy s id) := by
  have h1 : Safe s (s.modObj id (fun o =>
      { (Object.freshPlay mk o).cleared with controller := p, buffed := mk.buff })) :=
    Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  unfold enterBase
  split
  · exact h1.trans (setExhausted_safe true _ _)
  · exact h1

/-- The facts of playing the card for free: nothing was paid, so no additional cost was (Legion and
the turn are as for any play). -/
def GameState.freeMark (s : GameState) (p : PlayerId) (c : ObjId) : PlayMark :=
  { s.playMark p c ⟨0, []⟩ with paid := false, extraPaid := 0 }

/-- Play a card without paying its cost (CR 349): a Unit or a Gear goes to the Base of the player,
exhausted if it is a Unit that does not enter ready, and the play is noted, so that what waits for a
card to be played fires. A card that is in the Base already is played again where it is. -/
def playFree (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.cardDef? id with
  | some d =>
    -- only a Unit or a Gear enters the Base; a Spell is played by `playSpellStep`
    if !(d.hasType .unit || d.hasType .gear) || s.blocksPlay p id d then (s, []) else
    match moveObj s id (.player p .base) with
    | some r =>
      (enterBase p d (s.freeMark p id) (s.readyNow p id d) r.1 r.2,
        [Event.moved id r.2 (.player p .base), Event.played p r.2])
    | none =>
      if s.locate id = some (.player p .base) then
        (enterBase p d (s.freeMark p id) (s.readyNow p id d) s id, [Event.played p id])
      else (s, [])
  | none => (s, [])

/-- Playing a card without paying is a safe change. -/
theorem playFree_safe (p : PlayerId) (s : GameState) (id : ObjId) : Safe s (playFree p s id).1 := by
  unfold playFree
  split
  · split
    · exact Safe.refl s
    · split
      · rename_i d hd r hr
        exact (Safe.moveObj hr).trans (enterBase_safe _ _ _ _ _ _)
      · split
        · exact enterBase_safe _ _ _ _ _ _
        · exact Safe.refl s
  · exact Safe.refl s

/-- Recycle the cards one after the other, the first one first. -/
def recycleList : List ObjId → GameState → GameState × List Event
  | [], s => (s, [])
  | id :: ids, s =>
    let r := recycleOne s id
    let r2 := recycleList ids r.1
    (r2.1, r.2 ++ r2.2)

/-- Recycling cards is a safe change. -/
theorem recycleList_safe : ∀ (ids : List ObjId) (s : GameState), Safe s (recycleList ids s).1
  | [], s => Safe.refl s
  | id :: ids, s => (recycleOne_safe s id).trans (recycleList_safe ids _)

/-- Reveal from the top of the Main Deck until a card with the properties is revealed: it is played
for free, and the others revealed are recycled (all of the deck if no card matches). -/
def playFirstOf (fs : FilterList) (p : PlayerId) (src : ObjId) (env : Env) (s : GameState) :
    GameState × List Event :=
  let deck := s.zone (.player p .mainDeck)
  match deck.find? (fun id => fs.holds s src env id == some true) with
  | some u =>
    let r := playFree p s u
    let r2 := recycleList (deck.takeWhile (fun id => id != u)) r.1
    (r2.1, r.2 ++ r2.2)
  | none => recycleList deck s

/-- Playing the first card is a safe change. -/
theorem playFirstOf_safe (fs : FilterList) (p : PlayerId) (src : ObjId) (env : Env)
    (s : GameState) : Safe s (playFirstOf fs p src env s).1 := by
  unfold playFirstOf
  dsimp only
  split
  · exact (playFree_safe p s _).trans (recycleList_safe _ _)
  · exact recycleList_safe _ _

/-- Flow and some limited plays replace where a finalized Spell goes (CR 391.3.a, 829.1.b.1). -/
def Object.banishesOnChainExit (o : Object) : Bool :=
  o.flowed || (o.limitedSpellExit == .banish && o.pendingSpellPlay.isNone)

/-- The destination of a card removed from the Chain after replacement effects (CR 367-370). -/
def GameState.chainDestinationKind (s : GameState) (id : ObjId) (o : Object)
    (otherwise : ZoneKind) : ZoneKind :=
  if o.banishesOnChainExit then .banishment else s.ownerDestination id o otherwise

/-- A card leaving the Chain always goes to an owner's zone. -/
def GameState.chainDestination (s : GameState) (id : ObjId) (o : Object)
    (otherwise : ZoneKind) : Zone :=
  .player o.owner (s.chainDestinationKind id o otherwise)

/-- Attribute a banishing replacement to its controller, the card's owner (CR 391.3.a). -/
def GameState.chainExitEvents (s : GameState) (o : Object) (id new : ObjId)
    (otherwise : ZoneKind) : List Event :=
  let dest := s.chainDestinationKind id o otherwise
  o.ownerMoveEvents id new dest (o.banishesOnChainExit || otherwise != dest)

/-- Counter a spell: it leaves the Chain for the Trash of its owner without resolving (CR 359.3.d).
Nothing happens to what is not a spell on the Chain. -/
def counterObjTo (k : ZoneKind) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    if id ∈ s.zone .chain ∧ !(s.activeMods id).contains .uncounterable ∧
      !(s.controlledMods o.controller).contains .controlledItemsUncounterable then
      match o.kind with
      | .chainAbility .. =>
        -- a countered ability ceases to exist
        match removeObj s id with
        | some s2 => (s2, [])
        | none => (s, [])
      | _ =>
        match moveObj s id (s.chainDestination id o k) with
        | some r => (r.1, s.chainExitEvents o id r.2 k)
        | none => (s, [])
    else (s, [])
  | none => (s, [])

/-- Countering a spell or an ability is a safe change. -/
theorem counterObjTo_safe (k : ZoneKind) (s : GameState) (id : ObjId) :
    Safe s (counterObjTo k s id).1 := by
  unfold counterObjTo
  split
  · rename_i o ho
    split
    · split
      · split
        · rename_i s2 hr
          exact ⟨fun hwf => removeObj_wf hwf hr,
            fun hwf => removeObj_physIds hwf hr ho (by simp_all [ObjKind.phys?]),
            fun hwf hown => removeObj_ownerOk hwf hown hr, removeObj_sameMeta hr⟩
        · exact Safe.refl s
      · split
        · rename_i r hr
          exact Safe.moveObj hr
        · exact Safe.refl s
    · exact Safe.refl s
  · exact Safe.refl s

/-- Counter a spell: it goes to the Trash of its owner (CR 356). -/
def counterObj (s : GameState) (id : ObjId) : GameState × List Event := counterObjTo .trash s id

/-- Countering a spell is a safe change. -/
theorem counterObj_safe (s : GameState) (id : ObjId) : Safe s (counterObj s id).1 :=
  counterObjTo_safe .trash s id

/-- Counter a spell and return it to its owner's hand instead (Abandon). -/
def counterObjHand (s : GameState) (id : ObjId) : GameState × List Event :=
  counterObjTo .hand s id

/-- Countering a spell to the hand is a safe change. -/
theorem counterObjHand_safe (s : GameState) (id : ObjId) : Safe s (counterObjHand s id).1 :=
  counterObjTo_safe .hand s id

/-- Discard a card: it goes to the Trash of its owner, and the discard is noted (CR 423). -/
def discardObj (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := sendObj .trash s id
  match s.obj? id with
  | some o =>
    let discards := r.2.filterMap (fun e =>
      match e with
      | .moved _ n (.player _ .trash) => some (Event.discarded o.owner n true)
      | _ => none)
    ((if discards.isEmpty then r.1 else r.1.addTurnFx o.owner .cardDiscarded), r.2 ++ discards)
  | none => r

/-- Discarding a card is a safe change. -/
theorem discardObj_safe (s : GameState) (id : ObjId) : Safe s (discardObj s id).1 := by
  unfold discardObj
  split
  · dsimp only
    split
    · exact sendObj_safe .trash s id
    · exact (sendObj_safe .trash s id).trans (addTurnFx_safe _ _ _)
  · exact sendObj_safe .trash s id

/-- Record a linked trigger for each matching type after an actual discard. -/
def discardWithTypeEvents (p : PlayerId) (src : ObjId) (sourceCard : Option CardId)
    (links : List (CardType × Nat)) (s : GameState) (id : ObjId) : GameState × List Event :=
  let (next, events) := discardObj s id
  let linked := events.flatMap (fun
    | .discarded _ discarded _ =>
      match sourceCard, s.cardDef? id with
      | some card, some d => links.filterMap (fun (ty, idx) =>
          if d.hasType ty then some (.discardedTypeFor p src card idx discarded) else none)
      | _, _ => []
    | _ => [])
  (next, events ++ linked)

theorem discardWithTypeEvents_safe (p : PlayerId) (src : ObjId) (sourceCard : Option CardId)
    (links : List (CardType × Nat)) (s : GameState) (id : ObjId) :
    Safe s (discardWithTypeEvents p src sourceCard links s id).1 :=
  discardObj_safe s id

/-- Discard the selected hand cards to pay the cost before the ability enters the Chain (CR 423.3).
The last discard event closes the group for effects that watch one or more discards. -/
def payDiscards (p : PlayerId) : GameState → List ObjId → GameState × List Event
  | s, [] => (s, [])
  | s, id :: ids =>
    if (s.zone (.player p .hand)).contains id then
      let r := discardObj s id
      let next := payDiscards p r.1 ids
      let events := if ids.isEmpty then r.2 else r.2.map (fun e => match e with
        | .discarded q card _ => .discarded q card false
        | other => other)
      (next.1, events ++ next.2)
    else payDiscards p s ids

/-- Paying with hand cards preserves well-formedness, card identities and ownership. -/
theorem payDiscards_safe (p : PlayerId) :
    ∀ (ds : List ObjId) (s : GameState), Safe s (payDiscards p s ds).1
  | [], s => Safe.refl s
  | id :: ids, s => by
    simp only [payDiscards]
    split
    · exact (discardObj_safe s id).trans (payDiscards_safe p ids _)
    · exact payDiscards_safe p ids s

/-- Pay the optional discard after the mana payment, recording it on the card before the
play and discard triggers are processed (CR 357.1-357.2, 423.3). -/
def payPlayDiscard (p : PlayerId) (c : ObjId) (discard : Option ObjId)
    (r : GameState × List Event) : GameState × List Event :=
  match discard with
  | none => r
  | some id =>
    let paid := payDiscards p r.1 [id]
    let played := r.2.findSome? (fun
      | .moved old new _ => if old == c then some new else none
      | _ => none)
    (if paid.2.isEmpty then paid.1 else markPaid paid.1 played true, r.2 ++ paid.2)

/-- Paying the optional discard of a play preserves the structural invariants. -/
theorem payPlayDiscard_safe (p : PlayerId) (c : ObjId) (discard : Option ObjId)
    (r : GameState × List Event) : Safe r.1 (payPlayDiscard p c discard r).1 := by
  unfold payPlayDiscard
  split
  · exact Safe.refl _
  · dsimp only
    split
    · exact payDiscards_safe _ _ _
    · exact (payDiscards_safe _ _ _).trans (markPaid_safe _ _ true)

/-- Replacing a Rune Pool is a safe change. -/
theorem setPool_safe (s : GameState) (p : PlayerId) (pool : RunePool) : Safe s (s.setPool p pool) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Use the Rune abilities one after the other. -/
def applyRunes (s : GameState) (p : PlayerId) :
    List (ObjId × RuneAbility) → Option (GameState × List Event)
  | [] => some (s, [])
  | (r, ab) :: rest =>
    (applyRune s p r ab).bind (fun x =>
      (applyRunes x.1 p rest).map (fun y => (y.1, x.2 ++ y.2)))

/-- Using a Rune is a safe change. -/
theorem applyRune_safe {s s' : GameState} {p : PlayerId} {c : ObjId} {ab : RuneAbility}
    {es : List Event} (h : applyRune s p c ab = some (s', es)) : Safe s s' := by
  unfold applyRune at h
  split at h
  · rename_i o ho
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have h1 : Safe s (s.exhaustObj c) :=
        ⟨fun hwf => GameState.wf_exhaustObj hwf c,
         fun _ => (GameState.physIds_exhaustObj s c) ▸ List.Perm.refl _,
         fun _ hown => GameState.ownerOk_exhaustObj hown c, GameState.sameMeta_exhaustObj s c⟩
      exact h1.trans (setPool_safe _ _ _)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s2, id'⟩, hm, hr⟩ := h
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact (Safe.moveObj hm).trans (setPool_safe _ _ _)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Using Runes is a safe change. -/
theorem applyRunes_safe {p : PlayerId} :
    ∀ (plan : List (ObjId × RuneAbility)) {s s' : GameState} {es : List Event},
      applyRunes s p plan = some (s', es) → Safe s s'
  | [], s, s', es, h => by
    simp only [applyRunes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Safe.refl s
  | (r, ab) :: rest, s, s', es, h => by
    simp only [applyRunes, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, hr⟩ := h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact (applyRune_safe hx).trans (applyRunes_safe rest hy)

/-- Set the Pool and settle any eligible restricted Power spent on this payment. -/
def GameState.setPoolFor (s : GameState) (p : PlayerId) (src : ObjId) (pool : RunePool)
    (permanent : Bool := false) : GameState :=
  let t := s.setPool p pool
  let gear := (s.cardDef? src).any (·.hasType .gear)
  if gear || permanent then
    let spent := (s.poolOf p).any - pool.any
    { t with turnFx := s.spendPowerNotes p gear permanent spent t.turnFx }
  else t

/-- Setting the Pool after paying is a safe change. -/
theorem setPoolFor_safe (s : GameState) (p : PlayerId) (src : ObjId) (pool : RunePool)
    (permanent : Bool := false) : Safe s (s.setPoolFor p src pool permanent) := by
  unfold GameState.setPoolFor
  dsimp only
  split
  · exact (setPool_safe s p pool).trans
      ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
        fun _ hown => hown.congr rfl rfl, rfl⟩
  · exact setPool_safe s p pool

/-- Pay the cost `c` from eligible Pool resources, with Basic Runes if the Pool falls short. -/
def payByRunes (s : GameState) (p : PlayerId) (src : ObjId) (c : Cost)
    (unit : Bool := false) (permanent : Bool := false) (spell : Bool := false) :
    Option (GameState × List Event) :=
  match s.payNow p src c unit permanent spell with
  | some pool => some (s.setPoolFor p src pool permanent, [])
  | none =>
    match s.runePlan p src c unit permanent spell with
    | some plan =>
      (applyRunes s p plan).bind (fun r =>
        (r.1.payNow p src c unit permanent spell).map (fun pool => (r.1.setPoolFor p src pool permanent, r.2)))
    | none => none

/-- Paying is a safe change. -/
theorem payByRunes_safe {s : GameState} {p : PlayerId} {src : ObjId} {c : Cost}
    {unit permanent spell : Bool} {r : GameState × List Event}
    (h : payByRunes s p src c unit permanent spell = some r) : Safe s r.1 := by
  unfold payByRunes at h
  cases hp : s.payNow p src c unit permanent spell with
  | some pool =>
    simp only [hp, Option.some.injEq] at h
    rw [← h]
    exact setPoolFor_safe s p src pool permanent
  | none =>
    simp only [hp] at h
    cases hq : s.runePlan p src c unit permanent spell with
    | none => simp [hq] at h
    | some plan =>
      simp only [hq, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, hr⟩ := h
      cases hy : x.1.payNow p src c unit permanent spell with
      | none => simp [hy] at hr
      | some pool =>
        simp only [hy, Option.map_some, Option.some.injEq] at hr
        rw [← hr]
        exact (applyRunes_safe plan hx).trans (setPoolFor_safe _ _ _ _ permanent)

/-- Paying the first affordable cost option preserves the same invariants as the payment itself. -/
theorem payPlayOption_safe {s : GameState} {p : PlayerId} {id : ObjId} {costs : List Cost}
    {unit permanent : Bool} {r : GameState × List Event}
    (h : costs.findSome? (fun c => payByRunes s p id c unit permanent) = some r) :
    Safe s r.1 := by
  obtain ⟨_, _, _, _, paid, _⟩ := List.findSome?_eq_some_iff.mp h
  exact payByRunes_safe paid

/-- Play a card ignoring its Energy cost: its Power cost is paid from the Pool; if that cannot be
done, or the card is not a Unit or a Gear, nothing is paid and the card is not played. -/
def playPaying (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  if !((s.cardDef? id).any (fun d =>
      (d.hasType .unit || d.hasType .gear) && !s.blocksPlay p id d)) then (s, []) else
  match (s.cardDef? id).bind (·.cost) with
  | some c =>
    match (s.targetCostOptions p id [] ⟨0, s.adjustPower id c.power⟩).findSome? (fun price => payByRunes s p id price (permanent := true)) with
    | some r => ((playFree p r.1 id).1, r.2 ++ (playFree p r.1 id).2)
    | none => (s, [])
  | none => playFree p s id

/-- Playing a card for its Power is a safe change. -/
theorem playPaying_safe (p : PlayerId) (s : GameState) (id : ObjId) :
    Safe s (playPaying p s id).1 := by
  unfold playPaying
  split
  · exact Safe.refl s
  · split
    · split
      · rename_i r hr
        exact (payPlayOption_safe hr).trans (playFree_safe p _ id)
      · exact Safe.refl s
    · exact playFree_safe p s id

/-- Power that pays only for Gear and has been spent is no longer noted: only as much as the Pool
still holds stays noted (the Power that is added later is free to pay for anything). -/
def GameState.trimGear (s : GameState) (p : PlayerId) : GameState :=
  let noted :=
    (s.turnFx.filter (fun f => f.turn == s.turn && f.who == p && f.kind == .gearMana)).length
  { s with turnFx := dropGearFx s.turn p (noted - (s.poolOf p).any) s.turnFx }

/-- Trimming the note of Gear Power is a safe change. -/
theorem trimGear_safe (s : GameState) (p : PlayerId) : Safe s (s.trimGear p) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Add Power of any domain to the Pools of the players, one after the other. -/
def poolsAddAny (k : Nat) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, q :: qs =>
    let t := s.trimGear q
    poolsAddAny k (t.setPool q ((t.poolOf q).addAny k)) qs

/-- Adding Power is a safe change. -/
theorem poolsAddAny_safe (k : Nat) :
    ∀ (qs : List PlayerId) (s : GameState), Safe s (poolsAddAny k s qs)
  | [], s => Safe.refl s
  | q :: qs, s => ((trimGear_safe s q).trans (setPool_safe _ q _)).trans (poolsAddAny_safe k qs _)

/-- Change the Rune Pools of the players, one after the other. -/
def poolsMap (f : RunePool → RunePool) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, q :: qs => poolsMap f (s.setPool q (f (s.poolOf q))) qs

/-- Changing Rune Pools is a safe change. -/
theorem poolsMap_safe (f : RunePool → RunePool) :
    ∀ (qs : List PlayerId) (s : GameState), Safe s (poolsMap f s qs)
  | [], s => Safe.refl s
  | q :: qs, s => (setPool_safe s q _).trans (poolsMap_safe f qs _)

/-- Giving points is a safe change: the points are not part of what a safe change keeps. -/
theorem gainPoints_safe (s : GameState) (p : PlayerId) (n : Nat) : Safe s (s.gainPoints p n) :=
  ⟨fun hwf => GameState.wf_gainPoints hwf p n, fun _ => List.Perm.refl _,
    fun _ hown => GameState.ownerOk_gainPoints hown p n, rfl⟩

/-- The players gain points, one after the other. -/
def gainPointsAll (n : Nat) : GameState → List PlayerId → GameState
  | s, [] => s
  | s, p :: ps => gainPointsAll n (s.gainPoints p n) ps

/-- Giving points to any players is a safe change. -/
theorem gainPointsAll_safe (n : Nat) : ∀ (ps : List PlayerId) (s : GameState),
    Safe s (gainPointsAll n s ps)
  | [], s => Safe.refl s
  | p :: ps, s => (gainPoints_safe s p n).trans (gainPointsAll_safe n ps _)

/-- Channeling is a safe change. -/
theorem channel_safe (p : PlayerId) (n : Nat) (s : GameState) : Safe s (channel p n s).1 :=
  ⟨fun hwf => channel_wf p n hwf, fun hwf => channel_physIds p n hwf,
    fun hwf hown => channel_ownerOk p n hwf hown, channel_sameMeta p n s⟩

/-- The new identifiers of the objects that moved. -/
def movedNew : List Event → List ObjId
  | [] => []
  | .moved _ id _ :: es => id :: movedNew es
  | _ :: es => movedNew es

/-- Exhaust the objects. -/
def exhaustAll : List ObjId → GameState → GameState
  | [], s => s
  | id :: ids, s => exhaustAll ids (setExhausted true s id).1

/-- Exhausting objects is a safe change. -/
theorem exhaustAll_safe : ∀ (ids : List ObjId) (s : GameState), Safe s (exhaustAll ids s)
  | [], s => Safe.refl s
  | id :: ids, s => (setExhausted_safe true s id).trans (exhaustAll_safe ids _)

/-- Extra Runes supplied by replacement effects. Each active copy adds to the same instruction. -/
def GameState.channelBonuses (s : GameState) (p : PlayerId) (requested : Nat) : Nat :=
  if requested == 0 then 0 else
    ((s.controlledMods p).filterMap (fun
      | .additionalExhaustedRunes n => some n
      | _ => none)).sum

/-- Channel `n` Runes ready and the rest exhausted, including replacement effects (CR 431). -/
def channelEx (p : PlayerId) (n extra : Nat) (s : GameState) : GameState × List Event :=
  let r1 := channel p n s
  let r2 := channel p (extra + s.channelBonuses p (n + extra)) r1.1
  (exhaustAll (movedNew r2.2) r2.1, r1.2 ++ r2.2)

/-- Channeling some Runes exhausted is a safe change. -/
theorem channelEx_safe (p : PlayerId) (n extra : Nat) (s : GameState) :
    Safe s (channelEx p n extra s).1 :=
  ((channel_safe p n s).trans (channel_safe p (extra + s.channelBonuses p (n + extra)) _)).trans
    (exhaustAll_safe _ _)

/-- The players channel. -/
def channelAll (n extra : Nat) : GameState → List PlayerId → GameState × List Event
  | s, [] => (s, [])
  | s, p :: ps =>
    let r := channelEx p n extra s
    let r' := channelAll n extra r.1 ps
    (r'.1, r.2 ++ r'.2)

/-- Channeling for any players is a safe change. -/
theorem channelAll_safe (n extra : Nat) :
    ∀ (ps : List PlayerId) (s : GameState), Safe s (channelAll n extra s ps).1
  | [], s => Safe.refl s
  | p :: ps, s => (channelEx_safe p n extra s).trans (channelAll_safe n extra ps _)

/-- Move a Unit to its controller's Base once the move is allowed, counting it and emitting its
movement event (CR 447). -/
def moveHomeUnchecked (s : GameState) (u : ObjId) : GameState × List Event :=
  match s.obj? u with
  | some o =>
    match moveObj s u (.player o.controller .base) with
    | some r =>
      (r.1.modObj r.2 (fun x => ({ x with loc := none } : Object).countMove s.turn o.loc),
        [Event.standardMoved r.2 none])
    | none => (s, [])
  | none => (s, [])

/-- Moving an allowed Unit to its Base preserves the structural invariants. -/
theorem moveHomeUnchecked_safe (s : GameState) (u : ObjId) :
    Safe s (moveHomeUnchecked s u).1 := by
  unfold moveHomeUnchecked
  split
  · split
    · rename_i r hr
      exact (Safe.moveObj hr).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl))
    · exact Safe.refl s
  · exact Safe.refl s

/-- Move a Unit to the Base of its controller by an effect, unless the move is forbidden
(CR 447). -/
def moveHome (s : GameState) (u : ObjId) : GameState × List Event :=
  if ((s.obj? u).bind (·.loc)).any (fun bf => s.homeForbiddenFor u bf) then
    (s, [])
  else moveHomeUnchecked s u

/-- Moving home is a safe change. -/
theorem moveHome_safe (s : GameState) (u : ObjId) : Safe s (moveHome s u).1 := by
  unfold moveHome
  split
  · exact Safe.refl s
  · exact moveHomeUnchecked_safe s u

/-- Move a Unit to a place by an effect: a Battlefield (`some`) or its controller's Base. -/
def sendToLoc (loc : Option ObjId) (s : GameState) (u : ObjId) : GameState × List Event :=
  match loc with
  | some bf => sendToBf bf s u
  | none => moveHomeUnchecked s u

/-- Moving to a place is a safe change. -/
theorem sendToLoc_safe (loc : Option ObjId) (s : GameState) (u : ObjId) :
    Safe s (sendToLoc loc s u).1 := by
  cases loc with
  | none => exact moveHomeUnchecked_safe s u
  | some bf => exact sendToBf_safe bf s u

/-- A required move into an invalid Battlefield becomes a Recall. Read the destination from the
board before the move, so both sides of a swap use the same board (CR 449.2.c). -/
def moveOrRecall (before : GameState) (loc : Option ObjId) (s : GameState) (u : ObjId) :
    GameState × List Event :=
  if before.config.mode.isTeamDuel && loc.any (fun bf => (before.obj? u).any (fun o =>
      o.loc != some bf && ((before.cardDef? u).any (·.hasType .unit) || !o.unitGearEffects.isEmpty) &&
      !before.effectMoveBattlefieldOk o bf)) then recallFx false s u
  else sendToLoc loc s u

theorem moveOrRecall_safe (before : GameState) (loc : Option ObjId) (s : GameState) (u : ObjId) :
    Safe s (moveOrRecall before loc s u).1 := by
  unfold moveOrRecall
  split
  · exact recallFx_safe false s u
  · exact sendToLoc_safe loc s u

/-- A Unit's move protection applies to enemy effects while its ability is active, including
when it is granted by attached Equipment (CR 137, 451). -/
def GameState.blocksEnemyMove (s : GameState) (p : PlayerId) (u : ObjId) : Bool :=
  (s.obj? u).any (fun o => !s.config.mode.sameSide p o.controller) &&
    ((s.activeMods u).contains .noEnemyEffectMove ||
      s.inPlay.any (fun gear =>
        (s.obj? gear).any (·.attached == some u) &&
          (s.cardDef? gear).any (fun d => d.grants.any (fun
            | .passive .always mods => mods.contains .noEnemyEffectMove
            | _ => false))))

/-- Apply a move instructed by a spell or ability. In team play, a Unit going to an invalid
Battlefield is recalled instead (CR 449.2.c). -/
def moveByEffect (controller : PlayerId) (loc : Option ObjId) (s : GameState) (u : ObjId) :
    GameState × List Event :=
  if s.moveBlocked u || s.blocksEnemyMove controller u then (s, [])
  else match loc with
    | none => moveHome s u
    | some bf => moveOrRecall s (some bf) s u

/-- Applying or preventing an effect move preserves the structural invariants. -/
theorem moveByEffect_safe (p : PlayerId) (loc : Option ObjId) (s : GameState) (u : ObjId) :
    Safe s (moveByEffect p loc s u).1 := by
  unfold moveByEffect
  split
  · exact Safe.refl s
  · cases loc with
    | none => exact moveHome_safe s u
    | some bf => exact moveOrRecall_safe s (some bf) s u

/-- Two Units swap places by an effect: each goes to where the other is. Nothing happens if they are
at the same place or either move is forbidden. -/
def swapPlaces (s : GameState) (x y : ObjId) (controller : Option PlayerId := none) :
    GameState × List Event :=
  let lx := (s.obj? x).bind (·.loc)
  let ly := (s.obj? y).bind (·.loc)
  if s.moveBlocked x || s.moveBlocked y ||
      controller.any (fun p => s.blocksEnemyMove p x || s.blocksEnemyMove p y) ||
      lx == ly || (lx.isNone && ly.any (s.homeForbiddenFor y)) ||
      (ly.isNone && lx.any (s.homeForbiddenFor x)) then (s, [])
  else
    let r1 := moveOrRecall s ly s x
    let r2 := moveOrRecall s lx r1.1 y
    (r2.1, r1.2 ++ r2.2)

/-- Swapping places is a safe change. -/
theorem swapPlaces_safe (s : GameState) (x y : ObjId) (controller : Option PlayerId := none) :
    Safe s (swapPlaces s x y controller).1 := by
  unfold swapPlaces
  dsimp only
  split
  · exact Safe.refl s
  · exact (moveOrRecall_safe s _ s x).trans (moveOrRecall_safe s _ _ y)

/-- Play a card without paying, to a Battlefield. If it would put an outside Unit into a Combat,
play the Unit at its controller's Base (CR 464.2.a). -/
def playFreeAt (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := playFree p s id
  if (s.cardDef? id).any (·.hasType .unit) && !s.combatAllowsUnitPlay p bf then r
  else
    match movedNew r.2 with
    | n :: _ =>
      -- The card enters there directly, without any move events, state or triggers.
      (enterAtBattlefield s r.1 bf n, r.2)
    | [] => r

/-- Playing a card to a Battlefield is a safe change. -/
theorem playFreeAt_safe (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) :
    Safe s (playFreeAt p bf s id).1 := by
  unfold playFreeAt
  dsimp only
  split
  · exact playFree_safe p s id
  · cases movedNew (playFree p s id).2 with
    | nil => exact playFree_safe p s id
    | cons n _ =>
      exact (playFree_safe p s id).trans (enterAtBattlefield_safe s _ bf n)


/-- A Unit cannot be replayed by its owner to another player's Base (CR 419.4). -/
def GameState.foreignBase (s : GameState) (id : ObjId) (owner : PlayerId) : Bool :=
  match s.locate id with
  | some (.player player .base) => player != owner
  | _ => false

/-- Banish a Unit and play the resulting card as a new object, ignoring its cost. A token
ceases to exist when banished (CR 187, 420.3, 428). -/
def banishReplay (p : PlayerId) (s : GameState) (id : ObjId) (replay : BanishReplay := .byOwner) :
    GameState × List Event :=
  let r := banishObj p s id
  match r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none),
      (s.obj? id) with
  | some n, some o =>
    match o.kind with
    | .token _ => r
    | _ => if replay == .sameLocation && s.foreignBase id o.owner then r else
      let player := if replay == .toBase then p else o.owner
      let t := match if replay == .sameLocation then o.loc else none with
        | some bf => playFreeAt player bf r.1 n
        | none => playFree player r.1 n
      (t.1, r.2 ++ t.2)
  | _, _ => r

/-- Banishing a unit and playing it again is a safe change. -/
theorem banishReplay_safe (p : PlayerId) (s : GameState) (id : ObjId) (replay : BanishReplay) :
    Safe s (banishReplay p s id replay).1 := by
  unfold banishReplay
  dsimp only
  split
  · rename_i n o
    split
    · exact sendObj_safe .banishment s id
    · split
      · exact sendObj_safe .banishment s id
      · split
        · exact (sendObj_safe .banishment s id).trans (playFreeAt_safe _ _ _ _)
        · exact (sendObj_safe .banishment s id).trans (playFree_safe _ _ _)
  · exact sendObj_safe .banishment s id

/-- Play a card without paying, to a Battlefield: to its Base, if the opponents of the player play
Units only to their Base (Mageseeker Warden). -/
def playToOrBase (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if (s.cardDef? id).any (·.hasType .unit) &&
      (s.oppHas p .oppsPlayToBaseOnly || s.cantActHere p .play bf) then playFree p s id
  else playFreeAt p bf s id

/-- Playing a card to a Battlefield or to the Base is a safe change. -/
theorem playToOrBase_safe (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) :
    Safe s (playToOrBase p bf s id).1 := by
  unfold playToOrBase
  split
  · exact playFree_safe p s id
  · exact playFreeAt_safe p bf s id

/-- A Unit or Gear can be played by an effect to the location it specifies (CR 355.17.b). -/
def GameState.permanentPlayAllowed (s : GameState) (p : PlayerId) (id : ObjId)
    (d : CardDef) (dest : Option ObjId) : Bool :=
  (d.hasType .unit || d.hasType .gear) && !s.blocksPlay p id d &&
    dest.elim (!d.playsOnlyToBattlefield)
      (fun bf => d.canPlayAtBattlefield && s.playBfLocationAllowed p id d bf)

/-- Play a Unit or Gear with its Energy cost reduced by `k`. Check that the required destination
is legal before paying (CR 355.17.b, 358.5). -/
def playReducedOne (p : PlayerId) (k : Nat) (dest : Option ObjId) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if !(s.cardDef? id).any (fun d => s.permanentPlayAllowed p id d dest) then (s, []) else
  -- the cost the card is played for now (the other reductions count too), less `k` Energy
  match (s.cardDef? id).bind (fun d => s.effCost p id d) with
  | some c =>
    match (s.targetCostOptions p id [] (c.lessEnergy k)).findSome? (fun cost =>
        payByRunes s p id cost ((s.cardDef? id).any (·.hasType .unit)) (permanent := true)) with
    | some r =>
      let played := match dest with
        | some bf => playFreeAt p bf r.1 id
        | none => playFree p r.1 id
      (played.1, r.2 ++ played.2)
    | none => (s, [])
  | none =>
    match dest with
    | some bf => playFreeAt p bf s id
    | none => playFree p s id

/-- The legal locations satisfying maximal compatible sets of requirements (CR 355.17).
A requirement can be met alongside all others matched by a location only when a legal
location matches the larger set. -/
def effectPlayLocations (s : GameState) (p : PlayerId) (id : ObjId) (d : CardDef)
    (requirements : List (List (Option ObjId))) : List (Option ObjId) :=
  if requirements.isEmpty then
    (if d.playsOnlyToBattlefield then [] else [none]) ++ (s.playBfOptions p id).map some
  else
    let legal := requirements.flatten.eraseDups.filter (s.permanentPlayAllowed p id d)
    let satisfied (loc : Option ObjId) := requirements.map (·.contains loc)
    legal.filter (fun loc =>
      let kept := satisfied loc
      !legal.any (fun other =>
        let more := satisfied other
        kept != more && (kept.zip more).all (fun (wanted, present) => !wanted || present)))

/-- The adjusted base cost when an effect lets a card be played (CR 356.1). -/
def EffectPlayPrice.baseCost (price : EffectPlayPrice) (s : GameState) (p : PlayerId)
    (id : ObjId) (d : CardDef) : Option Cost :=
  match price with
  | .reduceEnergy _ => s.effCost p id d
  | .ignoreEnergy => d.cost.map (fun c => s.adjustCost p id { c with energy := 0 })
  | .ignoreBase => some (s.adjustCost p id Cost.zero)
  | .alternateBase cost => some (s.adjustCost p id cost)

/-- Any further reduction of optional and base Energy combined. -/
def EffectPlayPrice.energyCut : EffectPlayPrice → Nat
  | .reduceEnergy k => k
  | _ => 0

/-- Costs and destinations for a Unit or Gear played by an effect, before obtaining the resources
to pay (CR 355-357, 420.3). -/
def permanentPlayOptions (s : GameState) (p : PlayerId) (id : ObjId) (terms : EffectPlayTerms) :
    List ReducedPermanentPlay := Id.run do
  let some d := s.cardDef? id | return []
  if s.cantPlay p || s.blocksPlay p id d || !(d.hasType .unit || d.hasType .gear) ||
      d.hasType .spell then return []
  let some base := terms.price.baseCost s p id d | return []
  let extraObjects := none :: ((d.playExtra.toList.flatMap (fun (k, _) =>
    s.extraCandidates p k)).map some)
  let extras := extraObjects.map (·, SpellPick.plain) ++
    (if (s.zone (.player p .legendZone)).isEmpty && (s.playXPCost p d).isSome
      then [(none, .withXP .plain)] else [])
  let discardOptions := s.playDiscards p id
  let showOffOptions := none :: (s.showOffOptions p id d).map some
  let mut plans := []
  for battlefieldFees in [] :: s.battlefieldFeeChoices p id d do
    let requirements := terms.requirements ++ battlefieldFees.map (fun b => [some b])
    for battlefield in effectPlayLocations s p id d requirements do
      for (extraObject, extraPick) in extras do
        let extra := extraObject.toList
        if !s.extraOk p id extra extraPick then continue
        for cost in s.cutOptionsOf p id base extra extraPick do
          for (total, picked) in s.playCostPlans p id d cost do
            let additionalPaid := d.additionalCost.isSome && picked.contains 0
            let accelerated := s.accelerateForPlay p d &&
              picked.contains (if d.additionalCost.isSome then 1 else 0)
            for fee in s.battlefieldFeeTotals p d battlefieldFees do
              let combined := (total.plus fee).lessEnergy terms.price.energyCut
              for gearDiscounts in s.gearDiscountChoices p d do
                let cut := s.gearDiscountTotal p gearDiscounts
                for adjusted in s.targetCostOptions p id (battlefield.toList ++ extra) combined cut do
                  for pay in adjusted.payments d.domains do
                    let fixed : Cost := ⟨pay.energy, pay.power.map PowerSym.domain⟩
                    for discard in discardOptions do
                      for showOff in showOffOptions do
                        let plan : ReducedPermanentPlay := {
                          cost := fixed
                          battlefield
                          extraObject
                          discard
                          additionalPaid
                          accelerated
                          battlefieldFees
                          gearDiscounts
                          showOff
                          spendXP := extraPick.paysXP }
                        plans := plan :: plans
  return plans.reverse.eraseDups

/-- The legal finalizations that can already be funded with the Pool and Basic Runes. -/
def permanentPlayPlans (s : GameState) (p : PlayerId) (id : ObjId) (terms : EffectPlayTerms) :
    List ReducedPermanentPlay :=
  let unit := (s.cardDef? id).any (·.hasType .unit)
  (permanentPlayOptions s p id terms).filter (fun plan =>
    (payByRunes s p id plan.cost unit (permanent := true)).isSome)

/-- The possible reduced plays when the effect leaves the destination to the Unit's player. -/
def reducedPermanentPlays (s : GameState) (p : PlayerId) (id : ObjId) (less : Nat) :
    List ReducedPermanentPlay :=
  permanentPlayPlans s p id { price := .reduceEnergy less }

/-- Play a Unit or Gear with a chosen reduced-cost finalization. Emit the play after its costs
have been paid and return the identifier it acquired when it entered play. -/
def applyReducedPermanent (s : GameState) (p : PlayerId) (id : ObjId)
    (plan : ReducedPermanentPlay) : Option (GameState × ObjId × List Event) := do
  let d ← s.cardDef? id
  let paid ← payByRunes s p id plan.cost (d.hasType .unit) (permanent := true)
  let zone := plan.battlefield.elim (.player p .base) (fun _ => .battlefieldZone)
  let (onBoard, new) ← moveObj paid.1 id zone
  let ownCosts := (if plan.additionalPaid then [0] else []) ++
    (if plan.accelerated then [if d.additionalCost.isSome then 1 else 0] else [])
  let pick := if plan.battlefieldFees.isEmpty then SpellPick.plain
    else .payForBattlefield plan.battlefieldFees ownCosts
  let pick := if plan.gearDiscounts.isEmpty then pick else .withGearDiscounts pick plan.gearDiscounts
  let pick := if plan.spendXP then .withXP pick else pick
  let mark := { s.playMark p id ⟨plan.cost.energy, []⟩ with
    paid := if d.additionalCost.isSome then plan.additionalPaid else plan.accelerated
    extraPaid := ownCosts.length
    shownOff := s.captureShowOff p plan.showOff
    spellPick := pick }
  let ready := s.readyNow p id d mark.shownOff || plan.accelerated
  let spent := spendGearDiscounts onBoard p plan.gearDiscounts
  let moved := (enterBase p d mark ready spent new, [Event.moved id new zone])
  let placed := placeAtBf s plan.battlefield.toList moved
  let extra ← payExtra0 s id plan.extraObject.toList placed (if plan.spendXP then some p else none)
  let result := payPlayDiscard p id plan.discard extra
  some (result.1, new, s.showOffEvents p plan.showOff ++ paid.2 ++ result.2 ++ [Event.played p new])

/-- Reduced-cost finalization preserves the structural and ownership invariants. -/
theorem applyReducedPermanent_safe {s : GameState} {p : PlayerId} {id : ObjId}
    {plan : ReducedPermanentPlay} {r : GameState × ObjId × List Event}
    (h : applyReducedPermanent s p id plan = some r) : Safe s r.1 := by
  unfold applyReducedPermanent at h
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨d, hd, paid, hp, ⟨onBoard, new⟩, hm, extra, he, rfl⟩ := h
  exact (payByRunes_safe hp).trans ((Safe.moveObj hm).trans
    ((spendGearDiscounts_safe onBoard p plan.gearDiscounts).trans
      ((enterBase_safe _ _ _ _ _ _).trans ((placeAtBf_safe _ _ _).trans
        ((payExtra0_safe he).trans (payPlayDiscard_safe _ _ _ _))))))

/-- The new identity created by banishing the chosen card. -/
def banishedPlayId (es : List Event) : Option ObjId :=
  es.findSome? (fun
    | .moved _ id (.player _ .banishment) => some id
    | _ => none)

/-- Banish the player's top card and give its new object permission until their next Ending Phase. -/
def banishTopForPlay (s : GameState) (p : PlayerId) : GameState × List Event :=
  match (s.zone (.player p .mainDeck)).head? with
  | none => (s, [])
  | some card =>
    let banished := banishObj p s card
    let deadline := s.turnsTaken p + if s.active == some p && s.phase != .ending then 0 else 1
    match banishedPlayId banished.2 with
    | some next => (banished.1.modObj next (fun o => { o with playUntilEnding := some deadline }),
        banished.2)
    | none => banished

/-- Banishing a card and recording its play permission preserves the game invariants. -/
theorem banishTopForPlay_safe (s : GameState) (p : PlayerId) :
    Safe s (banishTopForPlay s p).1 := by
  unfold banishTopForPlay
  split
  · exact Safe.refl s
  · rename_i card h
    dsimp only
    split
    · exact (banishObj_safe p s card).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl))
    · exact banishObj_safe p s card

/-- Discover and project resource abilities for a card played by an effect. -/
structure EffectAddPolicy where
  /-- The next Adds that leave a way to reach a state satisfying the supplied funding check. -/
  choices : GameState → PlayerId → (GameState → Bool) → List EffectAdd
  /-- An upper bound on Power obtainable in this funding window. -/
  powerBudget : GameState → PlayerId → Nat
  /-- Project the chosen activations or commit them as part of the successful play. -/
  applyAll : GameState → PlayerId → List EffectAdd → Option (GameState × List Event)
  /-- A complete sequence of activations preserves the game invariants. -/
  safe : ∀ {s p adds r}, applyAll s p adds = some r → Safe s r.1

/-- Check a permanent's resource cost against the current Pool (CR 357.1). -/
def permanentPriceInPool (s : GameState) (p : PlayerId) (card : ObjId) (plan : ReducedPermanentPlay) :
    Bool :=
  let unit := (s.cardDef? card).any (·.hasType .unit)
  (s.payNow p card plan.cost unit (permanent := true)).isSome

/-- A previously selected finalization is still legal and its payment is in the Pool. -/
def permanentPlayReady (s : GameState) (p : PlayerId) (card : ObjId) (terms : EffectPlayTerms)
    (plan : ReducedPermanentPlay) : Bool :=
  permanentPriceInPool s p card plan && (permanentPlayOptions s p card terms).contains plan

/-- Find individual Add activations that can fund this permanent without invalidating its plan. -/
def permanentAddChoices (s : GameState) (p : PlayerId) (card : ObjId) (terms : EffectPlayTerms)
    (plan : ReducedPermanentPlay) (funding : EffectAddPolicy) : List EffectAdd :=
  if plan.cost.total == 0 then [] else
  let unit := (s.cardDef? card).any (·.hasType .unit)
  funding.choices s p (fun t => (payByRunes t p card plan.cost unit (permanent := true)).isSome &&
    (permanentPlayOptions t p card terms).contains plan)

/-- The finalizations that can be paid, with a flag for the choice of Add activations. -/
def fundablePermanentChoices (s : GameState) (p : PlayerId) (card : ObjId) (terms : EffectPlayTerms)
    (funding : EffectAddPolicy) : List (ReducedPermanentPlay × Bool) :=
  (permanentPlayOptions s p card terms).filterMap (fun plan =>
    let hasAdds := !(permanentAddChoices s p card terms plan funding).isEmpty
    if hasAdds || permanentPriceInPool s p card plan then some (plan, hasAdds) else none)

/-- A looked-at card may be offered only if it meets the filter, is still in the same deck,
and will have a legal finalization after leaving it for Banishment (CR 355.16, 420.3.c). -/
def lookedPlayCandidates (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (less : Nat) (fs : FilterList) (funding : EffectAddPolicy) : List ObjId :=
  let deck := s.zone (.player p .mainDeck)
  env.lookedCards.filter (fun id =>
    deck.contains id && FilterList.holds s src env id fs == some true &&
    (let banished := banishObj p s id
     (banishedPlayId banished.2).any (fun new =>
       !(fundablePermanentChoices banished.1 p new { price := .reduceEnergy less } funding).isEmpty)))

/-- Prepare the card for finalization, including a Banish if the play requires it. -/
def prepareFundedPlay (s : GameState) (p : PlayerId) (card : ObjId) (banish : Bool) :
    Option (GameState × ObjId × List Event) :=
  if banish then
    if (s.zone (.player p .mainDeck)).contains card then
      let result := banishObj p s card
      (banishedPlayId result.2).map (fun id => (result.1, id, result.2))
    else none
  else some (s, card, [])

theorem prepareFundedPlay_safe {s : GameState} {p : PlayerId} {card : ObjId} {banish : Bool}
    {r : GameState × ObjId × List Event} (h : prepareFundedPlay s p card banish = some r) :
    Safe s r.1 := by
  unfold prepareFundedPlay at h
  split at h
  · split at h
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
      exact banishObj_safe p s card
    · contradiction
  · cases h
    exact Safe.refl s

/-- Apply the selected Add activations and play together, committing only a legal finalization
(CR 358.5). -/
def finishFundedPermanentPlay (s : GameState) (p : PlayerId) (card : ObjId) (terms : EffectPlayTerms)
    (plan : ReducedPermanentPlay) (adds : List EffectAdd) (funding : EffectAddPolicy) :
    Option (GameState × ObjId × List Event) := do
  let (prepared, candidate, movement) ← prepareFundedPlay s p card terms.banishBeforeFunding
  let (funded, events) ← funding.applyAll prepared p adds
  if !permanentPlayReady funded p candidate terms plan then none else
    let (played, entered, finalEvents) ← applyReducedPermanent funded p candidate plan
    some (played, entered, movement ++ events ++ finalEvents)

/-- An atomic funded play preserves the game invariants. -/
theorem finishFundedPermanentPlay_safe {s : GameState} {p : PlayerId} {card : ObjId}
    {terms : EffectPlayTerms} {plan : ReducedPermanentPlay} {adds : List EffectAdd}
    {funding : EffectAddPolicy} {r : GameState × ObjId × List Event}
    (h : finishFundedPermanentPlay s p card terms plan adds funding = some r) : Safe s r.1 := by
  unfold finishFundedPermanentPlay at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨prepared, candidate, movement⟩, hprep, ⟨funded, events⟩, hfunded, h⟩ := h
  split at h
  · contradiction
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨played, entered, finalEvents⟩, hplayed, rfl⟩ := h
    have hsafe : Safe funded played :=
      applyReducedPermanent_safe (r := (played, entered, finalEvents)) hplayed
    exact (prepareFundedPlay_safe hprep).trans ((funding.safe hfunded).trans hsafe)

/-- Project the current payment and offer one more activation, payment from the available
resources, or abandonment of the optional play. The board is unchanged until confirmation. -/
def fundPermanentOptions (s : GameState) (p : PlayerId) (card : ObjId) (terms : EffectPlayTerms)
    (plan : ReducedPermanentPlay) (adds : List EffectAdd) (funding : EffectAddPolicy) :
    List Effect := Id.run do
  let some (prepared, candidate, _) := prepareFundedPlay s p card terms.banishBeforeFunding
    | return [.nop]
  let some (t, _) := funding.applyAll prepared p adds | return [.nop]
  let pay := if permanentPlayReady t p candidate terms plan then
      [.finishFundedPermanent card terms plan adds] else []
  let activate := (permanentAddChoices t p candidate terms plan funding).map (fun a =>
    Effect.fundPermanentFromEffect card terms plan (adds ++ [a]))
  return pay ++ activate ++ [.nop]

/-- Offer the finalization choices of a selected card. Banishment and Add activations commit
with the completed play. -/
def banishLookedStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (less : Nat)
    (es : EffectList) (funding : EffectAddPolicy) : GameState × List Frame × List Event :=
  let skip := (s, [.run p src env es], [Event.skipped src])
  match env.lookup pickVar with
  | some (.obj id) =>
    if env.lookedCards.contains id && (s.zone (.player p .mainDeck)).contains id then
      let r := banishObj p s id
      let terms : EffectPlayTerms := { price := .reduceEnergy less, banishBeforeFunding := true }
      let options := (banishedPlayId r.2).toList.flatMap (fun card =>
        fundablePermanentChoices r.1 p card terms funding)
      let choices := if options.any Prod.snd then
        options.map (fun (plan, _) => Effect.fundPermanentFromEffect id terms plan [])
      else options.map (fun (plan, _) => Effect.finishFundedPermanent id terms plan [])
      (s, [.run p src env (.cons (.eitherOf (EffectList.ofList choices)) es)], [])
    else skip
  | _ => skip

/-- Preparing or applying the Banish preserves the game invariants. -/
theorem banishLookedStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (less : Nat)
    (es : EffectList) (funding : EffectAddPolicy) :
    Safe s (banishLookedStep s p src env less es funding).1 := by
  unfold banishLookedStep
  split <;> (try split) <;> exact Safe.refl s

/-- Finalization choices and costs from the base price set by an effect (CR 420.3, 820.2). -/
def effectSpellOptions (s : GameState) (p : PlayerId) (id : ObjId) (d : CardDef)
    (e : EffectDef) (base : Cost) (energyCut : Nat) (powerBudget : Option Nat := none) :
    List (List ObjId × Cost × SpellPick) :=
  let costs := s.extrasRaw p id d
  let maximum := costs.countP Prod.snd
  let priced : List (List ObjId × Cost × SpellPick) := (s.variablePowerOptions p d powerBudget).flatMap (fun power =>
    let options := spellChoices s p id d e power
    (List.range (maximum + 1)).flatMap (fun count =>
      let selections := if d.usesRepeatChoices then repeatExecutions d options count else options
      selections.flatMap (fun (pick, ts) =>
        let surcharge := if s.playPowerCut p id ts == 0 then s.deflectCost p ts (some id) else 0
        (s.spellCostPlans p id d base ts pick).filterMap (fun (cost, (printed, repeats)) =>
          if repeats != count then none else
            let choice := if costs.isEmpty then pick else .withCosts pick printed repeats
            some (ts, { cost.lessEnergy energyCut with power := cost.power ++ List.replicate surcharge PowerSym.any },
              choice)))))
  (priced.flatMap (fun (ts, cost, pick) =>
    (s.spellPaymentPicks p d pick).filterMap (fun choice =>
      if d.spellObjectPreservesTargets ts choice then
        some (ts, cost.lessEnergy (s.spellExhaustDiscount p choice), choice)
      else none))).eraseDups

/-- A Spell on the Chain whose limited play has yet to finalize (CR 354.2, 354.3). -/
def GameState.pendingSpell (s : GameState) (card : ObjId) : Option PendingSpellPlay :=
  if (s.zone .chain).contains card then (s.obj? card).bind (·.pendingSpellPlay) else none

/-- The next Chain decision after a resolution. A queued play finalizes before anyone can respond. -/
def afterItem (s : GameState) : List Frame :=
  match (s.zone .chain).head? with
  | none => []
  | some card =>
    if (s.pendingSpell card).isSome then
      let p := ((s.obj? card).map (·.controller)).getD (s.active.getD ⟨0⟩)
      [.run p card {} (.cons (.finalizeLimitedSpell card) .nil)]
    else [.chainPass s.chainPrioritySeat 0]

/-- The frames under Cleanup after a resolution are play frames. -/
theorem afterItem_mem {s : GameState} {f : Frame} (h : f ∈ afterItem s) : f.isPlay = true := by
  unfold afterItem at h
  split at h
  · simp at h
  · split at h <;> obtain rfl := List.mem_singleton.mp h <;> rfl

/-- A Spell played by an effect cannot target the item still resolving or an unfinalized item
(CR 354.3, 355.9.a). -/
def limitedSpellOptions (s : GameState) (p : PlayerId) (card : ObjId)
    (price : EffectPlayPrice) (powerBudget : Option Nat := none) : List EffectSpellPlay := Id.run do
  let some d := s.cardDef? card | return []
  if !d.hasType .spell || s.cantPlay p || s.noSpells p || s.blocksPlay p card d then return []
  let some effect := d.spellEffect | return []
  let some base := price.baseCost s p card d | return []
  let resolving := s.pending.findSome? (fun | .finishSpell id => some id | _ => none)
  let discards := s.playDiscards p card
  return (effectSpellOptions s p card d effect base price.energyCut powerBudget).flatMap (fun (targets, cost, pick) =>
    if targets.all (fun id => resolving != some id && (s.pendingSpell id).isNone) then
      discards.map (fun discard => { targets, cost, pick, discard }) else [])

/-- Find individual Add activations that can pay for the Spell's chosen targets and mode. -/
def effectSpellAddChoices (s : GameState) (p : PlayerId) (card : ObjId) (price : EffectPlayPrice)
    (plan : EffectSpellPlay) (funding : EffectAddPolicy) : List EffectAdd :=
  if plan.cost.total == 0 then [] else
  funding.choices s p (fun t => (payByRunes t p card plan.cost (spell := true)).isSome &&
    (limitedSpellOptions t p card price (if (t.cardDef? card).any (·.variablePower) then
      some (funding.powerBudget t p) else none)).contains plan)

/-- Retain payable finalizations, recording whether an Add window is available for each. -/
def limitedSpellChoices (s : GameState) (p : PlayerId) (card : ObjId) (price : EffectPlayPrice)
    (funding : EffectAddPolicy) : List (EffectSpellPlay × Bool) :=
  let powerBudget := if (s.cardDef? card).any (·.variablePower) then some (funding.powerBudget s p) else none
  (limitedSpellOptions s p card price powerBudget).filterMap (fun plan =>
    let hasAdds := !(effectSpellAddChoices s p card price plan funding).isEmpty
    if hasAdds || (s.payNow p card plan.cost (spell := true)).isSome then some (plan, hasAdds) else none)

/-- Check the choices before paying the exact price from the Pool. -/
def effectSpellPoolPayment (s : GameState) (p : PlayerId) (card : ObjId) (price : EffectPlayPrice)
    (plan : EffectSpellPlay) : Option RunePool :=
  if (limitedSpellOptions s p card price).contains plan then s.payNow p card plan.cost (spell := true) else none

/-- Start a limited play by moving the card onto the Chain; its payment and targets wait
for the parent resolution (CR 354.2, 354.3). -/
def queueLimitedSpell (s : GameState) (p : PlayerId) (card : ObjId) (price : EffectPlayPrice)
    (exit : LimitedSpellExit) : Option (GameState × ObjId) := do
  let origin ← s.locate card
  let preceding := (s.zone origin).takeWhile (· != card)
  let (t, item) ← moveObj s card .chain
  let play := { price, origin, preceding : PendingSpellPlay }
  some (t.modObj item (fun o => { o with
    pendingSpellPlay := some play, limitedSpellExit := exit, controller := p }), item)

/-- Queuing a limited play preserves the game invariants. -/
theorem queueLimitedSpell_safe {s : GameState} {p : PlayerId} {card : ObjId}
    {price : EffectPlayPrice} {exit : LimitedSpellExit} {t : GameState} {item : ObjId}
    (h : queueLimitedSpell s p card price exit = some (t, item)) : Safe s t := by
  unfold queueLimitedSpell at h
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨origin, _, ⟨next, id⟩, moved, rfl, rfl⟩ := h
  exact (Safe.moveObj moved).trans (Safe.modObj _ id (fun _ => rfl) (fun _ => rfl))

/-- Playing a card for a reduced cost is a safe change. -/
theorem playReducedOne_safe (p : PlayerId) (k : Nat) (dest : Option ObjId) (s : GameState)
    (id : ObjId) : Safe s (playReducedOne p k dest s id).1 := by
  unfold playReducedOne
  split
  · exact Safe.refl s
  · split
    · split
      · rename_i r hr
        cases dest with
        | none => exact (payPlayOption_safe hr).trans (playFree_safe p _ id)
        | some bf => exact (payPlayOption_safe hr).trans (playFreeAt_safe p bf _ id)
      · exact Safe.refl s
    · cases dest with
      | none => exact playFree_safe p s id
      | some bf => exact playFreeAt_safe p bf s id
/-- The owner of an object has control of it again (CR 740). -/
def giveBack (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with controller := o.owner }), [])

/-- Giving control back is a safe change. -/
theorem giveBack_safe (s : GameState) (id : ObjId) : Safe s (giveBack s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- The object after it becomes a copy of an object of the kind: a token has the card of it. A card
stays what it is. -/
def copyKind (card : CardId) (x : Object) : Object :=
  match x.kind with
  | .token before => { x with kind := .token card, originalToken := x.originalToken <|> some before }
  | _ => x

/-- Becoming a copy keeps the physical card and the owner. -/
theorem copyKind_phys (card : CardId) (x : Object) :
    (copyKind card x).kind.phys? = x.kind.phys? ∧ (copyKind card x).owner = x.owner := by
  unfold copyKind
  split <;> simp_all [ObjKind.phys?]

/-- A token becomes a copy of another object: it has its card. A card stays what it is. -/
def becomeCopyOf (src : ObjId) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.cardDef? src with
  | some d => (s.modObj id (copyKind d.id), [])
  | none => (s, [])

/-- A change of one object that keeps its owner and the physical card it has (a token that
changes its card). -/
theorem Safe.modObjPhys (s : GameState) (id : ObjId) {f : Object → Object}
    (hk : ∀ o, (f o).kind.phys? = o.kind.phys?) (ho : ∀ o, (f o).owner = o.owner) :
    Safe s (s.modObj id f) :=
  ⟨fun h => GameState.wf_modObj h id f, fun _ => by
    have : (s.modObj id f).physIds = s.physIds := by
      unfold GameState.physIds
      apply filterMap_congr_mem
      intro x _
      rw [GameState.obj?_modObj]
      by_cases h : id.n = x.n
      · have hx : id = x := by cases id; cases x; simp_all
        subst hx
        cases s.obj? id <;> simp [hk]
      · simp [h]
    rw [this],
    fun _ h => GameState.ownerOk_modObj h id ho, GameState.sameMeta_modObj s id f⟩

/-- Becoming a copy is a safe change. -/
theorem becomeCopyOf_safe (src : ObjId) (s : GameState) (id : ObjId) :
    Safe s (becomeCopyOf src s id).1 := by
  unfold becomeCopyOf
  split
  · exact Safe.modObjPhys s id (fun x => (copyKind_phys _ x).1) (fun x => (copyKind_phys _ x).2)
  · exact Safe.refl s

/-- Add the Battlefield token to the board, if a Battlefield of the card is not there already. -/
def addBattlefieldTok (c : CardDef) (p : PlayerId) (s : GameState) : GameState :=
  if (s.zone .battlefieldZone).any (fun b => (s.cardDef? b).any (·.id == c.id)) then s
  else addTok s { kind := .token c.id, owner := p, controller := p, timestamp := ⟨0⟩ }
    .battlefieldZone

/-- Adding a Battlefield token is a safe change. -/
theorem addBattlefieldTok_safe (c : CardDef) (p : PlayerId) (s : GameState) :
    Safe s (addBattlefieldTok c p s) := by
  unfold addBattlefieldTok
  split
  · exact Safe.refl s
  · exact addTok_safe _ _ _ rfl

/-- A player takes control of an object (CR 740). -/
def setController (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  let s1 := s.modObj id (fun o => { o with controller := p })
  -- a Unit at a Battlefield makes it Contested by its new controller (CR 190.3)
  match (s.obj? id).bind (·.loc) with
  | some bf => (contestFor p bf s1, [])
  | none => (s1, [])

/-- Taking control is a safe change. -/
theorem setController_safe (p : PlayerId) (s : GameState) (id : ObjId) :
    Safe s (setController p s id).1 := by
  unfold setController
  have h1 : Safe s (s.modObj id (fun o => { o with controller := p })) :=
    Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  split
  · exact h1.trans (contestFor_safe _ _ _)
  · exact h1

/-- A player takes control of an object until the Unit of the card leaves the board. -/
def takeUntil (p : PlayerId) (card : Option ObjId) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  let r := setController p s id
  (r.1.modObj id (fun o => { o with takenBy := card }), r.2)

/-- Taking control until a Unit leaves is a safe change. -/
theorem takeUntil_safe (p : PlayerId) (card : Option ObjId) (s : GameState) (id : ObjId) :
    Safe s (takeUntil p card s id).1 :=
  (setController_safe p s id).trans (Safe.modObj _ id (fun _ => rfl) (fun _ => rfl))

/-- Players whose effects can replace this Unit's death with Banish. -/
def GameState.deathBanishers (s : GameState) (id : ObjId) : List PlayerId :=
  let marked := (s.turnFx.filter (·.appliesTo s.turn id .banishInstead)).map (·.who)
  let trash := ((s.obj? id).filter (s.replacesTrash id)).toList.map (·.owner)
  (marked ++ trash).eraseDups

/-- Offer the optional sacrifice while it is still available to the Unit (CR 371). -/
def GameState.deathSacrificeOptions (s : GameState) (p : PlayerId) (id : ObjId)
    (used : List (ObjId × Bool)) : List Effect :=
  if used.contains (id, true) || (s.deathSacrificeDecision id).isSome ||
      s.turnFx.any (·.appliesTo s.turn id .deathSacrificeUsed) ||
      !(s.activeMods id).contains .sacrificeToSaveSelf then []
  else (s.deathSacrificeUnits p id).map fun cost => .recordDeathSacrifice id (some cost)

/-- A declaration carries Banish attribution when Banish effects compete on their own.
The affected controller chooses separately whenever the Unit could also be rescued. -/
def GameState.deathBanisherOptions (s : GameState) (id : ObjId) : List (Option PlayerId) :=
  if (s.chosenDeathBanisher id).isSome || (s.automaticDeathSaver id).isSome ||
      (s.deathSacrificeDecision id).isSome ||
      (s.obj? id).any (fun o => !(s.deathSacrificeOptions o.controller id []).isEmpty) ||
      !(s.cardDef? id).any (·.hasType .unit) then [none] else
    match s.deathBanishers id with
    | first :: second :: rest => (first :: second :: rest).map some
    | _ => [none]

/-- The affected Unit's controller chooses the first applicable replacement (CR 372).
For an action cost, a Banish-only choice can already be part of the declaration. -/
def GameState.deathChoice (s : GameState) (id : ObjId) (used : List (ObjId × Bool))
    (offerBanish : Bool) : Option (ObjId × PlayerId × Effect × Effect) := do
  let unit ← s.obj? id
  if !(s.cardDef? id).any (·.hasType .unit) || (s.chosenDeathBanisher id).isSome ||
      (!used.contains (id, true) && (s.selectedDeathSacrifice id).isSome) then none
  else
    let gears := s.deathGearOptions id used
    if (s.chosenDeathGear id).any gears.contains || (s.selectedDeathFree id used).isSome then none
    else
      let free := s.deathFreeOptions id used
      let optional := s.deathSacrificeOptions unit.controller id used
      let banish := if offerBanish || !(gears.isEmpty && free.isEmpty && optional.isEmpty)
        then s.deathBanishers id else []
      let mandatory := gears.map (Effect.chooseDeathGear id) ++ free.map (Effect.chooseDeathFree id) ++
        banish.map (Effect.chooseDeathBanisher id)
      let choices := if mandatory.isEmpty && !optional.isEmpty
        then optional ++ [.recordDeathSacrifice id none] else mandatory ++ optional
      match choices with
      | first :: second :: rest =>
        let other := if rest.isEmpty then second else .eitherOf (EffectList.ofList (second :: rest))
        some (id, unit.controller, first, other)
      | _ => none

/-- Rewrite an answer or the answers behind a more-choices option. -/
def Effect.mapDeathOptions (map : Effect → Effect) (e : Effect) : Effect :=
  let rec mapList : EffectList → EffectList
    | .nil => .nil
    | .cons first rest => .cons (map first) (mapList rest)
  match e with
  | .eitherOf options => .eitherOf (mapList options)
  | other => map other

/-- Give one ordinary replacement answer its event scope. -/
def Effect.scopeDeathDecision (scope : ObjId → DeathDecision → Effect) : Effect → Effect
  | .chooseDeathBanisher unit player => scope unit (.banish player)
  | .chooseDeathGear unit source => scope unit (.gear source)
  | .chooseDeathFree unit source => scope unit (.free source)
  | .recordDeathSacrifice unit cost => scope unit (.sacrifice cost)
  | other => other

/-- Read the next outstanding choice in the same sequence used to resolve the Kill (CR 370.2). -/
def GameState.deathReplacementChoiceFrom (s : GameState) (root : ObjId) :
    Nat → ObjId → List (ObjId × Bool) → Bool → Option (ObjId × PlayerId × Effect × Effect)
  | 0, _, _, _ => none
  | fuel + 1, id, used, offerBanish =>
    let ready := prepareNestedDeath s root id used
    let ask := (ready.deathChoice id used offerBanish).map fun (unit, player, first, other) =>
      let scope := Effect.mapDeathOptions (Effect.scopeDeathDecision fun target choice =>
        .recordNestedDeathDecision root used target choice none)
      if used.isEmpty then (unit, player, first, other) else (unit, player, scope first, scope other)
    ask <|> match ready.deathSaveFor id used with
    | some save => save.cost.bind (fun cost =>
        s.deathReplacementChoiceFrom root fuel cost (save.useKey id :: used) true)
    | none => none

/-- Ask the controllers of the original and replacement Kills in order. -/
def GameState.deathReplacementChoice (s : GameState) (id : ObjId) (offerBanish : Bool := true) :
    Option (ObjId × PlayerId × Effect × Effect) :=
  s.deathReplacementChoiceFrom id (2 * s.inPlay.length + 1) id [] offerBanish

/-- Which deaths will be changed by an elected replacement or an automatic one. -/
def GameState.modifiedDeath (s : GameState) (id : ObjId) : Bool :=
  (s.deathSaveFor id []).isSome || s.banishedOnDeath id || (s.obj? id).any (s.replacesTrash id)

/-- A team-wide replacement is controlled by its source. The other replacements use the
affected Unit's seat unless a Banish source was recorded (CR 373.1). -/
def GameState.deathOrderController (s : GameState) (id : ObjId) : Option PlayerId :=
  let source := match s.deathSaveFor id [] with
    | some save =>
      if save.isSacrifice then none else
        match save.cost with
        | some gear =>
          if (s.activeMods gear).contains .diesInsteadOfFriendly then (s.obj? gear).map (·.controller)
          else none
        | none =>
          match s.freeDeathSaver id with
          | some (some rescuer) => (s.obj? rescuer).map (·.controller)
          | some none => (s.tacticalRetreatFor id).map (·.who)
          | none => none
    | none => s.chosenDeathBanisher id
  source <|> (s.obj? id).map (·.controller)

/-- Preserve the already determined prefix when a later Unit selects a different replacement. -/
def GameState.deathGroupPrefix (s : GameState) (group : List ObjId) : List ObjId :=
  ((s.turnFx.reverse.findSome? fun note =>
    if note.turn != s.turn then none else
      match note.kind with
      | .deathReselection g earlier _ | .nestedDeathDecision _ _ _ (some (g, earlier)) =>
        if g == group then some earlier else none
      | _ => none).getD []).filter group.contains

/-- The latest revision available at this point in the group's execution. -/
def GameState.deathReselectionAt (s : GameState) (group : List ObjId) (index : Nat)
    (id : ObjId) : Option (PlayerId × DeathDecision) :=
  s.turnFx.reverse.findSome? fun note =>
    if note.turn != s.turn || note.target != some id then none else
      match note.kind with
      | .deathReselection g earlier choice =>
        if g == group && earlier.length ≤ index then some (note.who, choice) else none
      | _ => none

/-- Make replacements chosen against the projected Board available to this root Kill. -/
def prepareDeathReselection (s : GameState) (group : List ObjId) (index : Nat)
    (id : ObjId) : GameState :=
  let rootNotes := match s.deathReselectionAt group index id with
    | none => s.turnFx
    | some choice => (s.applyDeathDecision id (some choice)).turnFx
  let nested := rootNotes.filterMap fun note =>
    if note.turn != s.turn then none else
      match note.kind with
      | .nestedDeathDecision root used choice (some (g, earlier)) =>
        if root == id && g == group && earlier.length ≤ index then
          some { note with kind := .nestedDeathDecision root used choice none }
        else none
      | _ => none
  { s with turnFx := rootNotes ++ nested }

theorem prepareDeathReselection_safe (s : GameState) (group : List ObjId) (index : Nat)
    (id : ObjId) : Safe s (prepareDeathReselection s group index id) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- The source of the selected survival effect, if it can replace another simultaneous death. -/
def GameState.deathSequenceSource (s : GameState) (id : ObjId) : Option DeathSequenceSource := do
  let save ← s.deathSaveFor id []
  if save.isSacrifice then none else
    match save.cost with
    | some gear => some (.gear gear)
    | none => (s.freeDeathSaver id).join.map .rescuer

/-- One root death, as seen after all preceding applications in the same group. -/
structure DeathGroupEntry where
  /-- The affected Unit. -/
  unit : ObjId
  /-- The number of earlier root events in this group. -/
  index : Nat
  /-- Sequences unavailable to this root death. -/
  closed : List DeathSequenceSource

/-- Use the choice valid at this position and exclude already completed sequences. -/
def DeathGroupEntry.prepare (entry : DeathGroupEntry) (group : List ObjId)
    (s : GameState) : GameState :=
  let ready := prepareDeathReselection s group entry.index entry.unit
  if entry.closed.isEmpty then ready
  else ready.addTurnFxOn (ready.active.getD ⟨0⟩) entry.unit (.closedDeathSequences entry.closed)

private theorem DeathGroupEntry.prepare_safe (entry : DeathGroupEntry) (group : List ObjId)
    (s : GameState) : Safe s (entry.prepare group s) := by
  unfold DeathGroupEntry.prepare
  split
  · exact prepareDeathReselection_safe s group entry.index entry.unit
  · exact (prepareDeathReselection_safe s group entry.index entry.unit).trans
      (addTurnFxOn_safe _ _ _ _)

/-- One root event. Its nested Kills can still use effects closed to simultaneous root events. -/
def applyGroupDeath (group : List ObjId) (g : GameState → ObjId → GameState × List Event)
    (s : GameState) (entry : DeathGroupEntry) : GameState × List Event :=
  let r := g (entry.prepare group s) entry.unit
  (if entry.closed.isEmpty then r.1 else clearClosedDeathSequences r.1, r.2)

private theorem applyGroupDeath_safe (group : List ObjId)
    {g : GameState → ObjId → GameState × List Event}
    (h : ∀ t id, Safe t (g t id).1) (s : GameState) (entry : DeathGroupEntry) :
    Safe s (applyGroupDeath group g s entry).1 := by
  unfold applyGroupDeath
  dsimp only
  split
  · exact (entry.prepare_safe group s).trans (h _ _)
  · exact ((entry.prepare_safe group s).trans (h _ _)).trans (clearClosedDeathSequences_safe _)

/-- One proposed root death and its next replacement on the projected Board. -/
structure DeathGroupCandidate where
  /-- The affected Unit. -/
  unit : ObjId
  /-- A replacement is available, including effects used only for this event. -/
  modified : Bool
  /-- A Board source whose sequence can continue on more than one event. -/
  sequence : Option DeathSequenceSource
  /-- The replacement's controller, when known. -/
  controller : Option PlayerId
  /-- The position of this controller's earlier ordering decision, if any. -/
  recorded : Option Nat

/-- Find the next applicable replacement of each remaining root. -/
def deathGroupCandidates (s : GameState) (group remaining : List ObjId)
    (index : Nat) (closed : List DeathSequenceSource) : List DeathGroupCandidate :=
  let recorded := s.turnFx.filter fun note => note.turn == s.turn && note.kind == .deathOrder group
  remaining.map fun unit =>
    let ready := (DeathGroupEntry.mk unit index closed).prepare group s
    let modified := ready.inPlay.contains unit && ready.modifiedDeath unit
    let controller := if modified then ready.deathOrderController unit else none
    ⟨unit, modified, if modified then ready.deathSequenceSource unit else none, controller,
      recorded.findIdx? (fun note => note.target == some unit && controller == some note.who)⟩

/-- Replacements act in turn order before simultaneous unmodified deaths (CR 373.1.a). -/
def sortDeathGroupCandidates (s : GameState) (candidates : List DeathGroupCandidate) :
    List DeathGroupCandidate :=
  let players := s.pickOrder
  let seat (c : DeathGroupCandidate) := (c.controller.bind players.idxOf?).getD s.playerCount
  candidates.mergeSort fun a b =>
    if a.modified != b.modified then a.modified
    else if !a.modified then true
    else if seat a != seat b then seat a < seat b
    else match a.recorded, b.recorded with
      | some x, some y => x ≤ y
      | none, some _ => false
      | _, none => true

/-- The Unit being acted on, the decision maker, and the first and remaining options. -/
abbrev DeathGroupChoice := ObjId × PlayerId × Effect × Effect

/-- The controller orders competing applications that can run next in this sequence. -/
def chooseDeathGroupOrder (group : List ObjId) (first : DeathGroupCandidate)
    (remaining : List DeathGroupCandidate) : Option DeathGroupChoice := do
  let controller ← first.controller
  if first.recorded.isSome then none else
    let others := ((remaining.filter fun c =>
      c.modified && c.recorded.isNone && c.controller == some controller).map (·.unit)).eraseDups
    match others.filter (· != first.unit) with
    | [] => none
    | second :: rest =>
      let choose := Effect.recordDeathOrder group
      let other := if rest.isEmpty then choose second
        else .eitherOf (EffectList.ofList ((second :: rest).map choose))
      some (first.unit, controller, choose first.unit, other)

/-- Record a revised choice against the prefix that made it necessary. -/
def scopeDeathGroupChoice (group prior : List ObjId)
    (choice : DeathGroupChoice) : DeathGroupChoice :=
  let scope := Effect.mapDeathOptions fun
    | .recordNestedDeathDecision root used target decision _ =>
      .recordNestedDeathDecision root used target decision (some (group, prior))
    | effect => effect.scopeDeathDecision (Effect.recordDeathReselection group prior)
  let (victim, player, first, other) := choice
  (victim, player, scope first, scope other)

/-- A stale decision may be revised to continue the open sequence before it closes. -/
def chooseOpenDeathSequence (group prior : List ObjId) (offerBanish : Bool)
    (active : DeathSequenceSource) (s : GameState) (remaining : List ObjId)
    (closed : List DeathSequenceSource) : Option DeathGroupChoice :=
  remaining.findSome? fun unit =>
    if !s.inPlay.contains unit then none else
      let ready := (DeathGroupEntry.mk unit prior.length closed).prepare group s
      let eligible := match active with
        | .gear source => (ready.deathGearOptions unit []).contains source
        | .rescuer source => (ready.deathFreeOptions unit []).contains (some source)
      if eligible then
        (ready.deathChoice unit [] offerBanish).map (scopeDeathGroupChoice group prior.reverse)
      else none

/-- A sequence continues while its selected effect applies to another root. Once it ends,
later roots can use other replacements but cannot restart that sequence (CR 373.2). -/
@[irreducible] def planDeathGroup (group : List ObjId) (offerChoices : Option Bool)
    (g : GameState → ObjId → GameState × List Event) :
    Nat → GameState → List ObjId → List ObjId → List ObjId →
    Option DeathSequenceSource → List DeathSequenceSource →
    List DeathGroupEntry × Option DeathGroupChoice
  | 0, _, _, _, _, _, _ => ([], none)
  | fuel + 1, s, remaining, prior, fixed, active, closed =>
    let openChoice := if fixed.isEmpty then offerChoices.bind fun offerBanish =>
        active.bind fun source => chooseOpenDeathSequence group prior offerBanish source s remaining closed
      else none
    if openChoice.isSome then ([], openChoice) else
    let candidates := deathGroupCandidates s group remaining prior.length closed
    let continuing := candidates.filter fun c => active.isSome && c.sequence == active
    let (closed, candidates) := if active.isSome && continuing.isEmpty then
        let closed := active.toList ++ closed
        (closed, deathGroupCandidates s group remaining prior.length closed)
      else (closed, if continuing.isEmpty then candidates else continuing)
    let ordered := sortDeathGroupCandidates s candidates
    let forced := fixed.head?.bind fun unit => candidates.find? (·.unit == unit) <|>
      (deathGroupCandidates s group [unit] prior.length closed).head?
    match forced <|> ordered.head? with
    | none => ([], none)
    | some chosen =>
      let entry : DeathGroupEntry := ⟨chosen.unit, prior.length, closed⟩
      let ask := offerChoices.bind fun offerBanish =>
        if forced.isSome then none else
          let ready := entry.prepare group s
          let revised := if !prior.isEmpty && ready.inPlay.contains entry.unit then
            (ready.deathReplacementChoice entry.unit offerBanish).map
              (scopeDeathGroupChoice group prior.reverse)
          else none
          revised <|> chooseDeathGroupOrder group chosen ordered
      match ask with
      | some choice => ([], some choice)
      | none => if fuel == 0 then ([entry], none) else
        let next := (applyGroupDeath group g s entry).1
        let (entries, choice) := planDeathGroup group offerChoices g fuel next
          (remaining.erase entry.unit) (entry.unit :: prior) fixed.tail chosen.sequence closed
        (entry :: entries, choice)

/-- Ask for choices, including any that depend on which earlier replacements can actually apply. -/
def GameState.deathGroupChoiceWith (s : GameState) (group : List ObjId) (offerBanish : Bool)
    (g : GameState → ObjId → GameState × List Event) : Option (ObjId × PlayerId × Effect × Effect) :=
  let earlier := s.deathGroupPrefix group
  let initial := if earlier.isEmpty then
      (sortDeathGroupCandidates s (deathGroupCandidates s group group 0 [])).findSome?
        (fun candidate => s.deathReplacementChoice candidate.unit offerBanish)
    else none
  initial <|> if 1 < group.length then
      (planDeathGroup group (some offerBanish) g group.length s group [] earlier none []).2
    else none

/-- A Trash replacement can still apply to a simultaneous kill after its own source was removed
by the same instruction (CR 370.1.a.2, 370.4). -/
def killOrSaveInGroup (before s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    if before.replacesTrash id o && !s.banishedOnDeath id &&
        (s.deathSaver id).isNone then banishObj o.owner s id
    else killOrSave s id
  | none => killOrSave s id

/-- A simultaneous kill with a surviving replacement is a safe change. -/
theorem killOrSaveInGroup_safe (before s : GameState) (id : ObjId) :
    Safe s (killOrSaveInGroup before s id).1 := by
  unfold killOrSaveInGroup
  split
  · split
    · exact banishObj_safe _ _ _
    · exact killOrSave_safe _ _
  · exact killOrSave_safe _ _

/-- Ask for replacement choices for a Kill instruction or declaration. -/
def GameState.deathGroupChoice (s : GameState) (group : List ObjId) (offerBanish : Bool := true) :
    Option (ObjId × PlayerId × Effect × Effect) :=
  s.deathGroupChoiceWith group offerBanish (killOrSaveInGroup s)

@[simp] theorem GameState.deathGroupChoiceWith_nil (s : GameState) (offerBanish : Bool)
    (g : GameState → ObjId → GameState × List Event) :
    s.deathGroupChoiceWith [] offerBanish g = none := by
  simp [GameState.deathGroupChoiceWith, GameState.deathGroupPrefix,
    deathGroupCandidates, sortDeathGroupCandidates]

@[simp] theorem GameState.deathGroupChoice_nil (s : GameState) (offerBanish : Bool) :
    s.deathGroupChoice [] offerBanish = none := s.deathGroupChoiceWith_nil offerBanish _

/-- Decisions about one simultaneous group do not carry over to the next group. -/
def clearDeathOrder (s : GameState) (group : List ObjId) : GameState :=
  { s with turnFx := s.turnFx.filter (fun note =>
      match note.kind with
      | .deathOrder g | .deathReselection g _ _ | .nestedDeathDecision _ _ _ (some (g, _)) =>
        g != group
      | _ => true) }

theorem clearDeathOrder_safe (s : GameState) (group : List ObjId) : Safe s (clearDeathOrder s group) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Apply all of the chosen replacements and deaths in one group. -/
def resolveDeathGroupWith (s : GameState) (group : List ObjId)
    (g : GameState → ObjId → GameState × List Event) : GameState × List Event :=
  let entries := (planDeathGroup group none g group.length s group [] (s.deathGroupPrefix group)
    none []).1
  let r := applyEach (applyGroupDeath group g) s entries
  (clearDeathOrder r.1 group, r.2)

theorem resolveDeathGroupWith_safe (s : GameState) (group : List ObjId)
    {g : GameState → ObjId → GameState × List Event}
    (h : ∀ t id, Safe t (g t id).1) : Safe s (resolveDeathGroupWith s group g).1 :=
  (applyEach_safe (applyGroupDeath_safe group h) _ s).trans
    (clearDeathOrder_safe _ group)

/-- An effect of this turn prevents the next damage to the object. -/
def GameState.shielded (s : GameState) (id : ObjId) : Bool :=
  s.turnFx.any (fun f => f.turn == s.turn && f.kind == .damagePrevented && f.target == some id)

/-- An effect of this turn doubles the damage dealt to the object. -/
def GameState.doubleDmg (s : GameState) (id : ObjId) : Bool :=
  s.turnFx.any (fun f => f.turn == s.turn && f.kind == .doubleDamage && f.target == some id)

/-- The prevention of the next damage to the object is used up. -/
def GameState.useShield (s : GameState) (id : ObjId) : GameState :=
  { s with turnFx := s.turnFx.eraseP (fun f =>
      f.turn == s.turn && f.kind == .damagePrevented && f.target == some id) }

/-- Using up a prevention is a safe change. -/
theorem useShield_safe (s : GameState) (id : ObjId) : Safe s (s.useShield id) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- The remaining finite Prevent Value on this Unit in the current turn (CR 438.3). -/
def GameState.preventValue (s : GameState) (id : ObjId) : Nat :=
  s.turnFx.foldl (fun sum f =>
    match f.kind with
    | .preventDamage k => if f.turn == s.turn && f.target == some id then sum + k else sum
    | _ => sum) 0

/-- Spend the Prevent Values on the Unit, in the order their effects were created (CR 438.3). -/
def spendPrevent (turn : Nat) (id : ObjId) : Nat → List TurnFx → List TurnFx
  | 0, notes => notes
  | _ + 1, [] => []
  | amount + 1, note :: rest =>
    match note.kind with
    | .preventDamage n =>
      if note.turn == turn && note.target == some id then
        if amount + 1 < n then { note with kind := .preventDamage (n - (amount + 1)) } :: rest
        else spendPrevent turn id (amount + 1 - n) rest
      else note :: spendPrevent turn id (amount + 1) rest
    | _ => note :: spendPrevent turn id (amount + 1) rest
termination_by _ notes => notes.length

/-- Spending a Prevent Value changes only the turn effects. -/
theorem spendPrevent_safe (s : GameState) (id : ObjId) (n : Nat) :
    Safe s { s with turnFx := spendPrevent s.turn id n s.turnFx } :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Record positive damage even if a subsequent game effect heals the object (CR 418-419). -/
def Object.takeDamage (o : Object) (turn n : Nat) : Object :=
  { o with damage := o.damage + n, damagedTurn := if n = 0 then o.damagedTurn else some turn }

/-- Damage is excluded by the Unit's immunity, with enemy-effect immunity scoped to its source. -/
def damageImmune (s : GameState) (id : ObjId) (o : Object) (controller : Option PlayerId) : Bool :=
  let mods := s.activeMods id
  mods.contains .noDamage ||
    (controller.any (fun p => !s.config.mode.sameSide p o.controller) && mods.contains .noEnemyEffectDamage)

/-- Record applied damage, then process effects that react directly to it (CR 418). -/
def dealRemaining (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  let damagingUnit := decide (0 < n) && (s.cardDef? id).any (·.hasType .unit)
  let lethal := (s.mightNow id).getD 0 ≤ ((s.obj? id).map (·.damage)).getD 0 + n
  let saver := if damagingUnit && decide lethal then s.deathSaver id else none
  let damaged := s.modObj id (fun o => o.takeDamage s.turn n)
  let event := Event.damaged id n
  match saver with
  | some _ =>
    let saved := killOrSave damaged id
    (saved.1, event :: saved.2)
  | none =>
    if damagingUnit && s.killOnHit id then
      let killed := killOrSave damaged id
      (killed.1, event :: killed.2)
    else (damaged, [event])

/-- Recording damage and applying direct reactions preserve the structural invariants. -/
theorem dealRemaining_safe (n : Nat) (s : GameState) (id : ObjId) :
    Safe s (dealRemaining n s id).1 := by
  have damaged := Safe.modObj s id (f := fun o => o.takeDamage s.turn n) (fun _ => rfl) (fun _ => rfl)
  unfold dealRemaining
  dsimp only
  split
  · exact damaged.trans (killOrSave_safe _ id)
  · split
    · exact damaged.trans (killOrSave_safe _ id)
    · exact damaged

/-- Preview the immediate damage path, where there is no choice of replacement order (CR 438.2-438.4). -/
def GameState.previewPrevent (s : GameState) (id : ObjId) (n : Nat) : Nat × Nat :=
  let incoming := if s.doubleDmg id then 2 * n else n
  let prevented := min incoming (s.preventValue id)
  (prevented, incoming - prevented)

/-- Spend finite prevention, then apply any damage left (CR 438.2-438.4). -/
def dealThroughPrevent (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  let (prevented, damage) := s.previewPrevent id n
  let after := { s with turnFx := spendPrevent s.turn id prevented s.turnFx }
  if 0 < n ∧ damage = 0 then (after, [])
  else dealRemaining damage after id

/-- Applying finite prevention preserves the structural invariants. -/
theorem dealThroughPrevent_safe (n : Nat) (s : GameState) (id : ObjId) :
    Safe s (dealThroughPrevent n s id).1 := by
  unfold dealThroughPrevent
  split
  split
  · exact spendPrevent_safe s id _
  · exact (spendPrevent_safe s id _).trans (dealRemaining_safe _ _ _)

/-- Apply damage after accounting for immunity, doubling and prevention (CR 418, 438). An object
whose damage reaches its Might is killed by the next Cleanup (CR 323.4), not here. -/
def dealObj (n : Nat) (s : GameState) (id : ObjId) (effectController : Option PlayerId := none) :
    GameState × List Event :=
  match s.obj? id with
  | some o =>
    if damageImmune s id o effectController then (s, [])
    else if decide (0 < n) && s.shielded id then (s.useShield id, [])
    else dealThroughPrevent n s id
  | none => (s, [])

/-- Dealing damage is a safe change. -/
theorem dealObj_safe (n : Nat) (s : GameState) (id : ObjId)
    (effectController : Option PlayerId := none) : Safe s (dealObj n s id effectController).1 := by
  unfold dealObj
  split
  · split
    · exact Safe.refl s
    · split
      · exact useShield_safe s id
      · exact dealThroughPrevent_safe n s id
  · exact Safe.refl s

/-- Read both Mights before marking damage. The Units themselves are the sources, so
modifiers for damage from a Spell do not apply (CR 418.6.b.3). -/
def exchangeDamage (s : GameState) (a b : ObjId) : GameState × List Event :=
  match s.mightNow a, s.mightNow b with
  | some am, some bm =>
    let hit := dealObj am.toNat s b
    let reply := dealObj bm.toNat hit.1 a
    (reply.1, hit.2 ++ reply.2)
  | _, _ => (s, [])

/-- The exchange keeps the structural invariants. -/
theorem exchangeDamage_safe (s : GameState) (a b : ObjId) :
    Safe s (exchangeDamage s a b).1 := by
  unfold exchangeDamage
  split
  · exact (dealObj_safe _ s b).trans (dealObj_safe _ _ a)
  · exact Safe.refl s

/-- How much has already been consumed from this turn note in the current damage instruction. -/
def EffectDamageBatch.spentOn (batch : EffectDamageBatch) (note : Nat) : Nat :=
  batch.spent.foldl (fun total (idx, amount) => if idx == note then total + amount else total) 0

/-- Find the still applicable replacements for one object, even when several copies of an
effect apply (CR 370.2, 372). -/
def damageReplacements (s : GameState) (batch : EffectDamageBatch) (target : ObjId) :
    List DamageReplacement :=
  s.turnFx.zipIdx.filterMap (fun (note, idx) =>
    if note.turn != s.turn || note.target != some target then none else
      match note.kind with
      | .doubleDamage => some .double
      | .preventDamage amount =>
        let remaining := amount - batch.spentOn idx
        if remaining == 0 then none else some (.prevent idx remaining)
      | .damagePrevented => if batch.spentOn idx == 0 then some (.shield idx) else none
      | _ => none)

/-- Apply one replacement to a positive incoming amount, or leave its effects unspent if
earlier replacements reduced the damage to zero (CR 370.2, 438.2, 438.4). -/
def DamageReplacement.applyAmount (replacement : DamageReplacement) (batch : EffectDamageBatch)
    (amount : Nat) : EffectDamageBatch × Nat :=
  if amount == 0 then (batch, 0) else
  match replacement with
  | .double => (batch, 2 * amount)
  | .prevent note remaining =>
    let spent := min amount remaining
    ({ batch with spent := (note, spent) :: batch.spent }, amount - spent)
  | .shield note => ({ batch with spent := (note, 1) :: batch.spent }, 0)

/-- Apply one replacement to the tentative damage event. -/
def chooseEffectDamage (batch : EffectDamageBatch) (hit : EffectDamageHit)
    (replacement : DamageReplacement) : EffectDamageBatch × EffectDamageHit :=
  let (next, amount) := replacement.applyAmount batch hit.amount
  (next, { hit with amount, replacements := hit.replacements.erase replacement })

/-- Effects with the same remaining value are interchangeable for this choice. -/
def DamageReplacement.sameChoice : DamageReplacement → DamageReplacement → Bool
  | .double, .double | .shield _, .shield _ => true
  | .prevent _ a, .prevent _ b => a == b
  | _, _ => false

/-- Store the chosen combat order, or keep asking while distinguishable replacements remain.
The note only records the order. No Prevent Value or shield is spent until damage is assigned. -/
def orderCombatDamageStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (target : ObjId) (chosen remaining : List DamageReplacement) (es : EffectList) :
    GameState × List Frame × List Event :=
  let options := remaining.eraseDupsBy DamageReplacement.sameChoice
  if 1 < options.length then
    let choices := options.map (fun r => Effect.orderCombatDamage target (r :: chosen) (remaining.erase r))
    (s, [.run p src env (.cons (.eitherOf (EffectList.ofList choices)) es)], [])
  else
    (s.addTurnFxOn p target (.combatDamageOrder (chosen.reverse ++ remaining)), [.run p src env es], [])

/-- Recording or continuing the combat order preserves the game invariants. -/
theorem orderCombatDamageStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (target : ObjId) (chosen remaining : List DamageReplacement) (es : EffectList) :
    Safe s (orderCombatDamageStep s p src env target chosen remaining es).1 := by
  unfold orderCombatDamageStep
  dsimp only
  split
  · exact Safe.refl s
  · exact addTurnFxOn_safe _ _ _ _

/-- A combat replacement decision only schedules more play frames. -/
theorem orderCombatDamageStep_mem {s : GameState} {p : PlayerId} {src target : ObjId}
    {env : Env} {chosen remaining : List DamageReplacement} {es : EffectList} {f : Frame}
    (hf : f ∈ (orderCombatDamageStep s p src env target chosen remaining es).2.1) :
    f.isPlay = true := by
  unfold orderCombatDamageStep at hf
  dsimp only at hf
  split at hf <;> obtain rfl := List.mem_singleton.mp hf <;> rfl

/-- Record the damage dealt by one instruction and collect all its damage events together. -/
def applyEffectDamageAmounts (s : GameState) : List (ObjId × Nat) → GameState × List Event
  | [] => (s, [])
  | (id, amount) :: rest =>
    let r := if (s.obj? id).isSome then dealRemaining amount s id else (s, [])
    let later := applyEffectDamageAmounts r.1 rest
    (later.1, r.2 ++ later.2)

/-- Recording a batch of damage preserves the game invariants. -/
theorem applyEffectDamageAmounts_safe (s : GameState) (hits : List (ObjId × Nat)) :
    Safe s (applyEffectDamageAmounts s hits).1 := by
  induction hits generalizing s with
  | nil => exact Safe.refl s
  | cons hit rest ih =>
    obtain ⟨id, amount⟩ := hit
    simp only [applyEffectDamageAmounts]
    split
    · exact (dealRemaining_safe amount s id).trans (ih _)
    · exact ih s

/-- Commit the spent effects and the damage in one step, after all replacement decisions. -/
def commitEffectDamage (s : GameState) (batch : EffectDamageBatch) : GameState × List Event :=
  let notes := s.turnFx.zipIdx.filterMap (fun (note, idx) =>
    let spent := batch.spentOn idx
    if spent == 0 then some note else
    match note.kind with
    | .preventDamage n =>
      if spent < n then some { note with kind := .preventDamage (n - spent) } else none
    | .damagePrevented => none
    | _ => some note)
  applyEffectDamageAmounts { s with turnFx := notes } batch.resolved.reverse

/-- Committing the ordered damage and its replacements preserves the game invariants. -/
theorem commitEffectDamage_safe (s : GameState) (batch : EffectDamageBatch) :
    Safe s (commitEffectDamage s batch).1 := by
  unfold commitEffectDamage
  dsimp only
  apply Safe.trans _ (applyEffectDamageAmounts_safe _ _)
  exact ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- A positive hit that immediately Kills a Unit or applies a lethal-damage replacement
can require a choice after prevention determines how much damage will be dealt. -/
def damageDeathChoice (s : GameState) (hit : ObjId × Nat) :
    Option (ObjId × PlayerId × Effect × Effect) :=
  let (id, amount) := hit
  let lethal := (s.mightNow id).getD 0 ≤ ((s.obj? id).map (·.damage)).getD 0 + amount
  if amount != 0 && (s.killOnHit id || (decide lethal && (s.deathSaver id).isSome)) then
    s.deathReplacementChoice id
  else none

/-- Combat assignment and damage replacement choices end once Combat Damage has been dealt. -/
def clearDamageOrder (s : GameState) : GameState :=
  { s with turnFx := s.turnFx.filter (fun note => match note.kind with
    | .combatDamageOrder _ | .combatAssignmentPriority _ => false
    | _ => true) }

/-- Forgetting the order of damage replacements changes no structural properties. -/
theorem clearDamageOrder_safe (s : GameState) : Safe s (clearDamageOrder s) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Note the excess damage of the player, in place of the note of an earlier Combat of the turn. -/
def noteExcess (s : GameState) (att : PlayerId) (k : Nat) : GameState :=
  { s with turnFx := s.turnFx.filter (fun f =>
      !(f.who == att && (match f.kind with | .excessDamage _ => true | _ => false))) ++
    [{ who := att, turn := s.turn, stamp := s.nextTimestamp, kind := .excessDamage k }] }

/-- Noting the excess damage is a safe change. -/
theorem noteExcess_safe (s : GameState) (att : PlayerId) (k : Nat) : Safe s (noteExcess s att k) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Finish recording a Combat's damage once it has been applied. -/
def recordCombatDamage (s : GameState) (att : PlayerId) (excess : Nat) : GameState :=
  noteExcess (clearDamageOrder s) att excess

/-- Finishing the damage bookkeeping preserves the game invariants. -/
theorem recordCombatDamage_safe (s : GameState) (p : PlayerId) (excess : Nat) :
    Safe s (recordCombatDamage s p excess) :=
  (clearDamageOrder_safe s).trans (noteExcess_safe _ p excess)

/-- Continue the damage instruction without applying its events until replacement ordering is
complete. A nonpositive result after prevention does not emit a damage event (CR 438.4). -/
def resolveEffectDamageStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (batch : EffectDamageBatch) (hit : Option EffectDamageHit) (es : EffectList) :
    GameState × List Frame × List Event :=
  let run (next : Effect) := (s, [Frame.run p src env (.cons next es)], [])
  match hit with
  | some damage =>
    if damage.amount == 0 then run (.resolveEffectDamage batch none)
    else if damage.replacements.isEmpty then
      run (.resolveEffectDamage { batch with resolved := (damage.target, damage.amount) :: batch.resolved } none)
    else
      let controller := ((s.obj? damage.target).map (·.controller)).getD p
      let options := (damage.replacements.eraseDupsBy DamageReplacement.sameChoice).map
        (Effect.chooseDamageReplacement batch damage)
      (s, [.run controller src env (.cons (.eitherOf (EffectList.ofList options)) .nil),
        .run p src env es], [])
  | none =>
    match batch.incoming with
    | [] =>
      match batch.resolved.reverse.findSome? (damageDeathChoice s) with
      | some (u, controller, first, other) =>
        (s, [.eitherDo controller u {} first other .nil,
          .run p src env (.cons (.resolveEffectDamage batch none) es)], [])
      | none =>
        let r := commitEffectDamage s batch
        (r.1, [.run p src env es], r.2)
    | (id, amount) :: rest =>
      let next := { batch with incoming := rest }
      match s.obj? id with
      | none => run (.resolveEffectDamage next none)
      | some target =>
        if damageImmune s id target batch.controller then run (.resolveEffectDamage next none)
        else if amount == 0 then
          run (.resolveEffectDamage { next with resolved := (id, 0) :: batch.resolved } none)
        else run (.resolveEffectDamage next (some ⟨id, amount, damageReplacements s batch id⟩))

/-- Ordering or committing an effect's damage preserves the game invariants. -/
theorem resolveEffectDamageStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (batch : EffectDamageBatch) (hit : Option EffectDamageHit) (es : EffectList) :
    Safe s (resolveEffectDamageStep s p src env batch hit es).1 := by
  unfold resolveEffectDamageStep
  split
  · split
    · exact Safe.refl s
    · split <;> exact Safe.refl s
  · split
    · split
      · exact Safe.refl s
      · exact commitEffectDamage_safe s batch
    · split
      · exact Safe.refl s
      · split
        · exact Safe.refl s
        · split <;> exact Safe.refl s

/-- The continuation of a damage instruction consists of play frames. -/
theorem resolveEffectDamageStep_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {batch : EffectDamageBatch} {hit : Option EffectDamageHit} {es : EffectList} {f : Frame}
    (hf : f ∈ (resolveEffectDamageStep s p src env batch hit es).2.1) : f.isPlay = true := by
  unfold resolveEffectDamageStep at hf
  split at hf
  · split at hf
    · obtain rfl := List.mem_singleton.mp hf
      rfl
    · split at hf
      · obtain rfl := List.mem_singleton.mp hf
        rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;> rfl
  · split at hf
    · split at hf
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;> rfl
      · obtain rfl := List.mem_singleton.mp hf
        rfl
    · split at hf
      · obtain rfl := List.mem_singleton.mp hf
        rfl
      · split at hf
        · obtain rfl := List.mem_singleton.mp hf
          rfl
        · split at hf <;> obtain rfl := List.mem_singleton.mp hf <;> rfl

/-- Use the ordered path when replacements interact. Otherwise keep the immediate path used by
ordinary damage and snapshot bonus damage and both Mights before any replacement choices. -/
def effectDamageBatch? (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (pr : Prim) :
    Option EffectDamageBatch := do
  if s.turnFx.length < 2 then none else
  let batch ← match pr with
    | .deal sel n => do
      if s.damageOff then none else
      let amount ← n.evalS s p src env
      let ids ← sel.eval s p src env
      let hits := ids.map (fun id =>
        (id, if amount == 0 then 0 else amount + s.bonusOn p src id env.sourceCard))
      some { controller := some (env.effectController.getD p), incoming := hits }
    | .exchangeDamage a b => do
      let x ← (← a.eval s p src env).head?
      let y ← (← b.eval s p src env).head?
      let xm ← s.mightNow x
      let ym ← s.mightNow y
      some { controller := none, incoming := [(y, xm.toNat), (x, ym.toNat)] }
    | _ => none
  if batch.incoming.any (fun (id, amount) => amount != 0 &&
      (s.obj? id).any (fun target => !damageImmune s id target batch.controller) &&
      (1 < (damageReplacements s batch id).length ||
        (damageDeathChoice s (id, amount)).isSome)) then some batch else none

/-- Apply the copyable text at the start of this attachment (CR 479.1.d, 719.1). -/
def copyAttachmentText (s : GameState) (g u : ObjId) (d : CardDef) : GameState :=
  let stamp : Timestamp := ⟨s.nextTimestamp⟩
  let copy : AttachmentCopy := ⟨g, d.id, stamp⟩
  let attached := s.modObj g (fun o => { o with attachmentTextStamp := some stamp })
  let copied := attached.modObj u (fun o =>
    { o with attachmentTextCopies := s.activeAttachmentText u ++ [copy] })
  { copied with nextTimestamp := s.nextTimestamp + 1 }

/-- Saving the copied Effect Text preserves structural invariants. -/
theorem copyAttachmentText_safe (s : GameState) (g u : ObjId) (d : CardDef) :
    Safe s (copyAttachmentText s g u d) := by
  let stamp : Timestamp := ⟨s.nextTimestamp⟩
  let copy : AttachmentCopy := ⟨g, d.id, stamp⟩
  let setStamp (o : Object) := { o with attachmentTextStamp := some stamp }
  let stamped := s.modObj g setStamp
  let setCopy (o : Object) := { o with attachmentTextCopies := s.activeAttachmentText u ++ [copy] }
  have h := (Safe.modObj s g (f := setStamp) (fun _ => rfl) (fun _ => rfl)).trans
    (Safe.modObj stamped u (f := setCopy) (fun _ => rfl) (fun _ => rfl))
  exact ⟨fun hwf => (h.wf hwf).congr rfl rfl rfl rfl, h.phys,
    fun hwf hown => (h.own hwf hown).congr rfl rfl, h.same⟩

/-- Attach an Equipment to a Unit (CR 137, 435). -/
def attachTo (u : ObjId) (s : GameState) (g : ObjId) : GameState × List Event :=
  if (s.obj? g).any (·.attached != some u) && !((s.cardDef? g).any (·.hasType .unit)) then
    let attach (o : Object) := { o with
      attached := some u, attachedTurn := some s.turn, attachmentCopyStamp := none,
      attachmentTextStamp := none }
    let t := s.modObj g attach
    let snapshot := if (s.cardDef? g).any CardDef.copiesUnitText then
      (s.cardDef? u).filter (·.hasType .unit) else none
    (snapshot.elim t (copyAttachmentText t g u), [Event.attached g u])
  else (s, [])

/-- Attaching is a safe change. -/
theorem attachTo_safe (u : ObjId) (s : GameState) (g : ObjId) : Safe s (attachTo u s g).1 := by
  unfold attachTo
  split
  · let attach (o : Object) := { o with
        attached := some u, attachedTurn := some s.turn, attachmentCopyStamp := none,
        attachmentTextStamp := none }
    have h := Safe.modObj s g (f := attach) (fun _ => rfl) (fun _ => rfl)
    apply h.trans
    dsimp only
    cases (if (s.cardDef? g).any CardDef.copiesUnitText then
      (s.cardDef? u).filter (·.hasType .unit) else none) with
    | none => exact Safe.refl _
    | some d => exact copyAttachmentText_safe _ g u d
  · exact Safe.refl s

/-- Capture the copyable traits of `model` for the current attachment (CR 479.1). -/
def copyAttachedUnit (g : ObjId) (s : GameState) (model : ObjId) : GameState × List Event :=
  match (s.obj? g).bind (·.attached), s.cardDef? model with
  | some unit, some d =>
    if model != unit && d.hasType .unit && (s.printedCardDef? unit).any (·.hasType .unit) &&
        s.inPlay.contains model && s.inPlay.contains unit then
      let stamp : Timestamp := ⟨s.nextTimestamp⟩
      let copy : AttachmentCopy := ⟨g, d.id, stamp⟩
      let source := s.modObj g (fun o => { o with attachmentCopyStamp := some stamp })
      let copied := source.modObj unit (fun o =>
        { o with attachmentCopies := copy :: o.attachmentCopies.filter (source.attachmentCopyActive unit) })
      ({ copied with nextTimestamp := s.nextTimestamp + 1 }, [])
    else (s, [])
  | _, _ => (s, [])

/-- Installing a copy preserves the object's physical identity and ownership. -/
theorem copyAttachedUnit_safe (g : ObjId) (s : GameState) (model : ObjId) :
    Safe s (copyAttachedUnit g s model).1 := by
  unfold copyAttachedUnit
  split
  · rename_i unit d _ _
    split
    · let stamp : Timestamp := ⟨s.nextTimestamp⟩
      let copy : AttachmentCopy := ⟨g, d.id, stamp⟩
      let setStamp (o : Object) := { o with attachmentCopyStamp := some stamp }
      let stamped := s.modObj g setStamp
      let setCopy (o : Object) := { o with
        attachmentCopies := copy :: o.attachmentCopies.filter (stamped.attachmentCopyActive unit) }
      have h := (Safe.modObj s g (f := setStamp) (fun _ => rfl) (fun _ => rfl)).trans
        (Safe.modObj stamped unit (f := setCopy) (fun _ => rfl) (fun _ => rfl))
      exact ⟨fun hwf => (h.wf hwf).congr rfl rfl rfl rfl, h.phys,
        fun hwf hown => (h.own hwf hown).congr rfl rfl, h.same⟩
    · exact Safe.refl s
  · exact Safe.refl s

/-- Double Might this turn by adding its current amount, with a minimum increase of zero
(CR 433.1, 479.4.c). -/
def doubleObj (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.mightNow id with
  | some m => (s.modObj id (fun o => { o with mightMods := o.mightMods ++ [⟨max 0 m, .turn⟩] }), [])
  | none => (s, [])

/-- Doubling the Might is a safe change. -/
theorem doubleObj_safe (s : GameState) (id : ObjId) : Safe s (doubleObj s id).1 := by
  unfold doubleObj
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- The activated ability described by a grant, when the referenced definition contains one. -/
def GameState.grantedActivation (s : GameState) (grant : AbilityGrant) : Option Ability :=
  match (s.cards.find? grant.card).bind (fun d =>
    if grant.borrowed then d.fullAbilities[grant.index]?
    else if grant.copyStamp.isSome then d.textAbilities[grant.index]? else d.grants[grant.index]?) with
  | some (a@(.activated ..)) => some a
  | _ => none

/-- Each friendly source with a continuous Legend grant contributes its own abilities. -/
def GameState.legendActivations (s : GameState) (legend : ObjId) (d : CardDef) :
    List (Option AbilityGrant × Ability) :=
  if d.hasType .legend then
    match s.obj? legend with
    | some recipient =>
      s.passiveSources.flatMap (fun src =>
        match s.obj? src, s.cardDef? src with
        | some donor, some card =>
          if donor.controller == recipient.controller &&
              card.fullAbilities.any (fun
                | .passive .always mods => mods.contains .grantFriendlyLegendsActivations
                | _ => false) then
            card.grants.zipIdx.filterMap (fun
              | (ability@(.activated ..), index) =>
                some (some { card := card.id, index, sourceStamp := some donor.timestamp }, ability)
              | _ => none)
          else []
        | _, _ => [])
    | none => []
  else []

/-- Own abilities keep their indices, followed by temporary, attachment and continuous grants. -/
def GameState.nativeActivationList (s : GameState) (src : ObjId) (d : CardDef) :
    List (Option AbilityGrant × Ability) :=
  let grants := ((s.obj? src).map (·.tempActivations)).getD []
  d.fullAbilities.map (none, ·) ++ grants.filterMap
    (fun grant => (s.grantedActivation grant).map (some grant, ·)) ++
    (s.attachmentTextDefs src).flatMap (fun (cd, stamp) =>
      cd.textAbilities.zipIdx.filterMap (fun
        | (ability@(.activated ..), index) =>
          some (some { card := cd.id, index, copyStamp := some stamp }, ability)
        | _ => none)) ++
    s.legendActivations src d

/-- Exhaust abilities gained from friendly Legends, Units and Gear (CR 727.1.b.1). -/
def GameState.friendlyExhaustActivations (s : GameState) (src : ObjId) (p : PlayerId) :
    List (Option AbilityGrant × Ability) :=
  s.passiveSources.flatMap (fun donor =>
    match s.obj? donor, s.cardDef? donor with
    | some o, some d =>
      if donor != src && o.controller == p &&
          (d.hasType .legend || d.hasType .unit || d.hasType .gear) then
        let stamp := (s.copyStamp? donor).getD o.timestamp
        (s.nativeActivationList donor d).zipIdx.filterMap (fun
          | ((grant, ability@(.activated costs _ _ _)), index) =>
            if costs.contains .exhaustSelf then
              some (some (grant.getD {
                card := d.id, index, copyStamp := some stamp, borrowed := true }), ability)
            else none
          | _ => none)
      else []
    | _, _ => [])

/-- The activated abilities of the object, including the definitions it gains from other objects. -/
def GameState.activationList (s : GameState) (src : ObjId) (d : CardDef) :
    List (Option AbilityGrant × Ability) :=
  s.nativeActivationList src d ++
    (if d.fullAbilities.any (fun
        | .passive .always mods => mods.contains .friendlyExhaustAbilities
        | _ => false)
     then s.friendlyExhaustActivations src (s.controllerOf src)
     else [])

/-- The available ability at its activation-menu index. -/
def GameState.activationAt (s : GameState) (src : ObjId) (idx : Nat) :
    Option (Option AbilityGrant × Ability) :=
  (s.cardDef? src).bind (fun d => (s.activationList src d)[idx]?)

/-- Give a board object an instance of the activated ability for the turn (CR 479.3). -/
def grantActivationObj (grant : AbilityGrant) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if (s.locate id).any Zone.isBoard && (s.grantedActivation grant).isSome then
    (s.modObj id (fun o => { o with tempActivations := o.tempActivations ++ [grant] }), [])
  else (s, [])

/-- Adding an activated ability to an object preserves structural invariants. -/
theorem grantActivationObj_safe (grant : AbilityGrant) (s : GameState) (id : ObjId) :
    Safe s (grantActivationObj grant s id).1 := by
  unfold grantActivationObj
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- Set the Unit's base Might without changing other effects on its Might (CR 479.2). -/
def setBaseMight (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  if (s.cardDef? id).any (·.hasType .unit) then
    (s.modObj id (fun o => { o with baseMightThisTurn := some n }), [])
  else (s, [])

/-- Changing the base Might preserves the structural invariants. -/
theorem setBaseMight_safe (n : Nat) (s : GameState) (id : ObjId) : Safe s (setBaseMight n s id).1 := by
  unfold setBaseMight
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- Detach an Equipment: it is attached to nothing. -/
def detachObj (s : GameState) (g : ObjId) : GameState × List Event :=
  (s.modObj g (fun o => { o with attached := none }), [])

/-- Detaching is a safe change. -/
theorem detachObj_safe (s : GameState) (g : ObjId) : Safe s (detachObj s g).1 :=
  Safe.modObj s g (fun _ => rfl) (fun _ => rfl)

/-- When detaching upon animation, use the attached permanent's actual place. The permanent
stays on the Board, so this bookkeeping emits no Move event (CR 143.5.b, 718.6.a). -/
def placeAnimatedGear (s : GameState) (p : PlayerId) (g : ObjId) (field : Option ObjId) :
    GameState × ObjId :=
  (moveObj s g (field.elim (.player p .base) (fun _ => .battlefieldZone))).getD (s, g)

/-- Placing the animated Gear keeps the physical cards and zones well formed. -/
theorem placeAnimatedGear_safe (s : GameState) (p : PlayerId) (g : ObjId) (field : Option ObjId) :
    Safe s (placeAnimatedGear s p g field).1 := by
  unfold placeAnimatedGear
  cases h : moveObj s g (field.elim (.player p .base) (fun _ => .battlefieldZone)) with
  | none => exact Safe.refl s
  | some result => exact Safe.moveObj h

/-- Apply the Unit and Might traits, detach the chosen Gear, and contest its Battlefield if needed
(CR 143.5, 190.3.a, 479). -/
def animateGearObject (s : GameState) (p : PlayerId) (source g : ObjId) : GameState :=
  match s.obj? g, s.cardDef? g with
  | some o, some d =>
    if s.inPlay.contains g && o.controller == p && d.hasType .gear then
      let field := o.attached.elim o.loc (fun attached => (s.obj? attached).bind (·.loc))
      let placed := placeAnimatedGear s p g field
      let might := (d.cost.map (·.energy)).getD 0
      let changed := placed.1.modObj placed.2 (fun gear => { gear with
        unitGearEffects := (source, might) :: gear.unitGearEffects.filter (fun fx => fx.1 != source)
        loc := field
        attached := none
        attachedTurn := none
        attachmentCopyStamp := none
        attachmentTextStamp := none })
      field.elim changed (fun bf => contestFor p bf changed)
    else s
  | _, _ => s

/-- Animation changes traits and position without changing ownership or the card's identity. -/
theorem animateGearObject_safe (s : GameState) (p : PlayerId) (source g : ObjId) :
    Safe s (animateGearObject s p source g) := by
  unfold animateGearObject
  split
  · rename_i o d _ _
    split
    · dsimp only
      cases o.attached.elim o.loc (fun attached => (s.obj? attached).bind (·.loc)) with
      | none =>
        refine (placeAnimatedGear_safe s p g none).trans ?_
        exact Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl)
      | some field =>
        refine (placeAnimatedGear_safe s p g (some field)).trans (Safe.trans ?_ (contestFor_safe p field _))
        exact Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl)
    · exact Safe.refl s
  · exact Safe.refl s

/-- End this source's earlier animation when a different target is finalized, before anyone
can respond to the new ability. Other Legends' effects still apply (CR 355.5, 479). -/
def endGearAnimation (s : GameState) (source chosen : ObjId) : GameState :=
  s.mapObjectsAt (fun id o => if id == chosen then o else
    { o with unitGearEffects := o.unitGearEffects.filter (fun fx => fx.1 != source) })

/-- Ending an animation preserves all structural invariants. -/
theorem endGearAnimation_safe (s : GameState) (source chosen : ObjId) :
    Safe s (endGearAnimation s source chosen) := by
  let keep (id : ObjId) (o : Object) := if id == chosen then o else
    { o with unitGearEffects := o.unitGearEffects.filter (fun fx => fx.1 != source) }
  have kind : ∀ id o, (keep id o).kind = o.kind := by
    intro id o
    unfold keep
    split <;> rfl
  have owner : ∀ id o, (keep id o).owner = o.owner := by
    intro id o
    unfold keep
    split <;> rfl
  exact ⟨fun hwf => GameState.wf_mapObjectsAt hwf keep,
    fun _ => (s.physIds_mapObjectsAt kind) ▸ List.Perm.refl _,
    fun _ h => GameState.ownerOk_mapObjectsAt h owner, rfl⟩

/-- Attach the objects the first selector stands for to the one the second stands for. `none` if
the second is not exactly one object, or either cannot be answered. -/
def applyAttach (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (gears to : Selector) :
    Option (GameState × List Event) :=
  (gears.eval s p src env).bind (fun gs =>
    (to.eval s p src env).bind (fun tos =>
      match tos with
      | [u] => some (applyEach (attachTo u) s gs)
      | _ => none))

/-- Attaching objects is a safe change. -/
theorem applyAttach_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {gears to : Selector} {r : GameState × List Event}
    (h : applyAttach s p src env gears to = some r) : Safe s r.1 := by
  unfold applyAttach at h
  cases hg : gears.eval s p src env with
  | none => simp [hg] at h
  | some gs =>
    cases ht : to.eval s p src env with
    | none => simp [hg, ht] at h
    | some tos =>
      simp only [hg, ht, Option.bind_some] at h
      cases tos with
      | nil => simp at h
      | cons u rest =>
        cases rest with
        | nil =>
          simp only [Option.some.injEq] at h
          rw [← h]
          exact applyEach_safe (fun s id => attachTo_safe u s id) gs s
        | cons _ _ => simp at h

/-- Remove up to `less` generic Power symbols from the Equip cost (CR 821.1.c.3). -/
def Cost.weaponmasterDiscount (c : Cost) (less : Nat) : Cost :=
  { c with power := Nat.repeat (fun symbols => symbols.erase .any) less c.power }

/-- Attach the Equipment to the unit, paying the Equip cost of each, less `less` generic Power
(Weaponmaster): an Equipment whose cost cannot be paid stays where it is, and one with no Equip
cost is not attached. `none` if the unit is not exactly one object, or either cannot be
answered. -/
def applyAttachPaying (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (gears to : Selector) (less : Nat) : Option (GameState × List Event) :=
  (gears.eval s p src env).bind (fun gs =>
    (to.eval s p src env).bind (fun tos =>
      match tos with
      | [u] =>
        if u ∈ s.inPlay then
        some (gs.foldl (fun (r : GameState × List Event) g =>
          match (r.1.cardDef? g).bind CardDef.equipCost with
          | some c =>
            match payByRunes r.1 p g (c.weaponmasterDiscount less) with
            | some q => ((attachTo u q.1 g).1, r.2 ++ q.2 ++ (attachTo u q.1 g).2)
            | none => r
          | none => r) (s, []))
        else some (s, [])
      | _ => none))

/-- Attaching Equipment for a cost is a safe change. -/
theorem applyAttachPaying_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {gears to : Selector} {less : Nat} {r : GameState × List Event}
    (h : applyAttachPaying s p src env gears to less = some r) : Safe s r.1 := by
  unfold applyAttachPaying at h
  cases hg : gears.eval s p src env with
  | none => simp [hg] at h
  | some gs =>
    cases ht : to.eval s p src env with
    | none => simp [hg, ht] at h
    | some tos =>
      simp only [hg, ht, Option.bind_some] at h
      cases tos with
      | nil => simp at h
      | cons u rest =>
        cases rest with
        | nil =>
          by_cases hu : u ∈ s.inPlay
          · simp only [hu, ite_true, Option.some.injEq] at h
            rw [← h]
            have key : ∀ (l : List ObjId) (r0 : GameState × List Event), Safe s r0.1 →
                Safe s (l.foldl (fun (r : GameState × List Event) g =>
                  match (r.1.cardDef? g).bind CardDef.equipCost with
                  | some c =>
                    match payByRunes r.1 p g (c.weaponmasterDiscount less) with
                    | some q => ((attachTo u q.1 g).1, r.2 ++ q.2 ++ (attachTo u q.1 g).2)
                    | none => r
                  | none => r) r0).1 := by
              intro l
              induction l with
              | nil => intro r0 h0; exact h0
              | cons g rest ih =>
                intro r0 h0
                simp only [List.foldl_cons]
                apply ih
                cases hc : (r0.1.cardDef? g).bind CardDef.equipCost with
                | none => simpa [hc] using h0
                | some c =>
                  cases hp : payByRunes r0.1 p g (c.weaponmasterDiscount less) with
                  | none => simpa [hc, hp] using h0
                  | some q =>
                    simp only [hp]
                    exact h0.trans ((payByRunes_safe hp).trans (attachTo_safe u _ g))
            exact key gs (s, []) (Safe.refl s)
          · simp only [hu, ite_false, Option.some.injEq] at h
            rw [← h]
            exact Safe.refl s
        | cons _ _ => simp at h

/-- A Unit token the player plays enters ready: an effect of the turn says the units the player
plays enter ready ("Friendly units enter ready this turn"), or a passive ability of an object they
control says their tokens do. -/
def GameState.tokenReady (s : GameState) (p : PlayerId) (c : CardDef)
    (dest : Option ObjId := none) : Bool :=
  c.hasType .unit && ((s.fxOf p).any (fun k => k == .unitsReady) ||
    s.anyActive .allUnitsEnterReady || s.readyAtDestination p dest ||
    -- a passive ability of an object the player controls: "your tokens enter ready"
    s.passiveSources.any (fun g => (s.obj? g).any (·.controller == p) &&
      (s.activeMods g).any (fun m =>
        match m with
        | .entersReady (.pick .all .friendly .anywhere fs) => fs == FilterList.ofList [.token]
        | _ => false)))

/-- The tokens played between two states are the new token objects (CR 184.2). -/
def tokenPlays (s s' : GameState) (p : PlayerId) : List Event :=
  (List.range (s'.nextId - s.nextId)).filterMap (fun i =>
    let id : ObjId := ⟨s.nextId + i⟩
    match s.obj? id, (s'.obj? id).map Object.kind with
    | none, some (ObjKind.token _) => some (.tokenPlayed p id)
    | _, _ => none)

/-- A Unit played as a token is buffed. -/
def buffTokenEv (t : GameState) (e : Event) : GameState :=
  match e with
  | .tokenPlayed _ id =>
    if (t.cardDef? id).any (·.hasType .unit) then
      t.modObj id (fun o => { o with buffed := true })
    else t
  | _ => t

/-- Buffing a token is a safe change. -/
theorem buffTokenEv_safe (t : GameState) (e : Event) : Safe t (buffTokenEv t e) := by
  unfold buffTokenEv
  split
  · split
    · exact Safe.modObj t _ (fun _ => rfl) (fun _ => rfl)
    · exact Safe.refl t
  · exact Safe.refl t

/-- Buffing the tokens that were played is a safe change. -/
theorem foldl_buffTokenEv_safe : ∀ (l : List Event) (t : GameState),
    Safe t (l.foldl buffTokenEv t)
  | [], t => Safe.refl t
  | e :: l, t => (buffTokenEv_safe t e).trans (foldl_buffTokenEv_safe l _)

/-- Buff the new Unit tokens that are covered by this turn's effects. -/
def buffNewTokens (s r : GameState) (p : PlayerId) : GameState :=
  let tokens := tokenPlays s r p
  let fx := s.fxOf p
  if fx.contains .unitsBuffed then tokens.foldl buffTokenEv r
  else if fx.contains .nextUnitAnywhereBuffed then
    let units := tokens.filter (fun
      | .tokenPlayed _ id => (r.cardDef? id).any (·.hasType .unit)
      | _ => false)
    (units.take 1).foldl buffTokenEv r
  else r

/-- Buffing the new tokens is a safe change. -/
theorem buffNewTokens_safe (s r : GameState) (p : PlayerId) : Safe r (buffNewTokens s r p) := by
  unfold buffNewTokens
  dsimp only
  split
  · exact foldl_buffTokenEv_safe _ r
  · split
    · exact foldl_buffTokenEv_safe _ r
    · exact Safe.refl r

/-- The locations a Unit token can be played to. Its controller may use their Base or a Battlefield
they control, and effects can grant or restrict Battlefield permissions (CR 184.2, 355.2). -/
def GameState.unitTokenDestinations (s : GameState) (p : PlayerId) (c : CardDef) :
    List (Option ObjId) :=
  let preview := createOne c.id p none false s
  let extra := preview.playBfOptions p ⟨s.nextId⟩
  let fields := (s.zone .battlefieldZone).filter (fun bf =>
    (s.cardDef? bf).any (·.hasType .battlefield) &&
    !s.oppHas p .oppsPlayToBaseOnly && !s.cantActHere p .play bf && s.combatAllowsUnitPlay p bf &&
    FilterList.holds s bf {} bf (.cons .unitsPlayable .nil) == some true &&
    ((s.obj? bf).any (·.control == some p) || extra.contains bf))
  none :: fields.map some

/-- Play a Unit token at a valid destination. -/
def playUnitTokenAt (s : GameState) (p : PlayerId) (name : String) (dest : Option ObjId) :
    GameState × List Event :=
  match s.tokenCard name with
  | some c =>
    if c.hasType .unit && (s.unitTokenDestinations p c).contains dest then
      let r := createOne c.id p dest (s.tokenReady p c dest) s
      let next := dest.elim r (fun bf => contestFor p bf r)
      (buffNewTokens s next p, tokenPlays s next p)
    else (s, [])
  | none => (s, [])

/-- Playing a Unit token at its destination is a safe change. -/
theorem playUnitTokenAt_safe (s : GameState) (p : PlayerId) (name : String) (dest : Option ObjId) :
    Safe s (playUnitTokenAt s p name dest).1 := by
  unfold playUnitTokenAt
  split
  · rename_i c _
    split
    · have place := createOne_safe c.id p dest (s.tokenReady p c dest) s
      cases dest with
      | none => exact place.trans (buffNewTokens_safe _ _ _)
      | some bf => exact place.trans ((contestFor_safe p bf _).trans (buffNewTokens_safe _ _ _))
    · exact Safe.refl s
  · exact Safe.refl s

/-- Play tokens: `n` of them on the player's Base or here, if the token is in the game's cards
(CR 183). `none` if it cannot be done yet. -/
def applyCreate (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (name : String)
    (n : Amount) (place : Place) (ready : Bool) : Option (GameState × List Event) :=
  (n.evalS s p src env).bind (fun k =>
    match s.tokenCard name with
    | none => none
    | some c =>
      match place with
      | .atBase =>
        let r := createN c.id p none (ready || s.tokenReady p c) k s
        some (buffNewTokens s r p, tokenPlays s r p)
      | .here =>
        match s.hereOf src with
        | some bf =>
          let location := if c.hasType .unit && !s.combatAllowsUnitPlay p bf then none else some bf
          let r := createN c.id p location (ready || s.tokenReady p c location) k s
          some (buffNewTokens s r p, tokenPlays s r p)
        | none =>
          -- at a Base, "here" is that Base
          if s.baseHere src then
            let r := createN c.id p none (ready || s.tokenReady p c) k s
            some (buffNewTokens s r p, tokenPlays s r p)
          else none
      | _ => none)

/-- Playing tokens is a safe change. -/
theorem applyCreate_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {name : String}
    {n : Amount} {place : Place} {ready : Bool} {r : GameState × List Event}
    (h : applyCreate s p src env name n place ready = some r) : Safe s r.1 := by
  unfold applyCreate at h
  cases hn : n.evalS s p src env with
  | none => simp [hn] at h
  | some k =>
    simp only [hn, Option.bind_some] at h
    cases ht : s.tokenCard name with
    | none => simp [ht] at h
    | some c =>
      simp only [ht] at h
      cases place with
      | atBase =>
        simp only [Option.some.injEq] at h
        rw [← h]
        exact (createN_safe _ _ _ _ _ _).trans (buffNewTokens_safe _ _ _)
      | here =>
        cases hh : s.hereOf src with
        | none =>
          simp only [hh] at h
          split at h
          · simp only [Option.some.injEq] at h
            rw [← h]
            exact (createN_safe _ _ _ _ _ _).trans (buffNewTokens_safe _ _ _)
          · simp at h
        | some bf =>
          simp only [hh, Option.some.injEq] at h
          rw [← h]
          exact (createN_safe _ _ _ _ _ _).trans (buffNewTokens_safe _ _ _)
      | anywhere => simp at h
      | boardOrLegend => simp at h
      | atBattlefield => simp at h
      | inHand => simp at h
      | inTrash => simp at h
      | inMainDeck => simp at h
      | inRuneDeck => simp at h
      | inChampionZone => simp at h
      | inLegendZone => simp at h
      | inHidden => simp at h
      | inBanishment => simp at h
      | inCombat => simp at h
      | onChain => simp at h
      | onChainAll => simp at h

/-- A token can be played at an instructed Battlefield if it passes the placement rules. -/
def GameState.tokenFieldAllowed (s : GameState) (p : PlayerId) (src : ObjId)
    (card : CardDef) (field : ObjId) : Bool :=
  card.canPlayAtBattlefield && s.playBfLocationAllowed p src card field

/-- Play tokens at the specified Battlefield. Unit tokens redirected to Base by a Combat
do not contest the Battlefield (CR 184.2, 190.3, 464.2.a, 830). -/
def applyCreateAt (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (name : String) (n : Amount) (dest : Selector) (ready : Bool) : Option (GameState × List Event) :=
  (n.evalS s p src env).bind fun count =>
    (s.tokenCard name).bind fun card =>
      ((dest.eval s p src env).bind List.head?).map fun field =>
        let redirected := card.hasType .unit && !s.combatAllowsUnitPlay p field
        if redirected || s.tokenFieldAllowed p src card field then
          let location := if redirected then none else some field
          let placed := createN card.id p location (ready || s.tokenReady p card location) count s
          let next := if card.hasType .unit && count > 0 && !redirected then contestFor p field placed else placed
          (buffNewTokens s next p, tokenPlays s next p)
        else (s, [])

/-- Playing the selected group of tokens preserves structural and physical-card invariants. -/
theorem applyCreateAt_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {name : String} {n : Amount} {dest : Selector} {ready : Bool} {r : GameState × List Event}
    (h : applyCreateAt s p src env name n dest ready = some r) : Safe s r.1 := by
  unfold applyCreateAt at h
  cases hn : n.evalS s p src env with
  | none => simp [hn] at h
  | some count =>
    cases hc : s.tokenCard name with
    | none => simp [hn, hc] at h
    | some card =>
      cases hd : dest.eval s p src env with
      | none => simp [hn, hc, hd] at h
      | some fields =>
        cases fields with
        | nil => simp [hn, hc, hd] at h
        | cons field fields =>
          simp only [hn, hc, hd, Option.bind_some, List.head?_cons, Option.map_some] at h
          split at h
          · cases h
            let location := if card.hasType .unit && !s.combatAllowsUnitPlay p field then none else some field
            have placed := createN_safe card.id p location (ready || s.tokenReady p card location) count s
            change Safe s (buffNewTokens s _ p)
            split
            · exact placed.trans ((contestFor_safe _ _ _).trans (buffNewTokens_safe _ _ _))
            · exact placed.trans (buffNewTokens_safe _ _ _)
          · cases h
            exact Safe.refl _

/-- Play tokens at the Battlefield the object left by its last move, or at the Base (Lillia). -/
def applyCreateAtPrev (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (name : String)
    (n : Amount) (ready : Bool) : Option (GameState × List Event) :=
  (n.evalS s p src env).bind (fun k =>
    (s.tokenCard name).map (fun c =>
      let dest := ((s.obj? src).bind (·.prevLoc)).filter (fun bf =>
        !c.hasType .unit || s.combatAllowsUnitPlay p bf)
      let r := createN c.id p dest (ready || s.tokenReady p c dest) k s
      (buffNewTokens s r p, tokenPlays s r p)))

/-- Playing tokens at the place an object came from is a safe change. -/
theorem applyCreateAtPrev_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {name : String} {n : Amount} {ready : Bool} {r : GameState × List Event}
    (h : applyCreateAtPrev s p src env name n ready = some r) : Safe s r.1 := by
  unfold applyCreateAtPrev at h
  cases hn : n.evalS s p src env with
  | none => simp [hn] at h
  | some k =>
    simp only [hn, Option.bind_some] at h
    cases ht : s.tokenCard name with
    | none => simp [ht] at h
    | some c =>
      simp only [ht, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact (createN_safe _ _ _ _ _ _).trans (buffNewTokens_safe _ _ _)

/-- Play one more token like the one the object is, where it is. -/
def cloneTok (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    match o.kind with
    | .token c =>
      let card := (s.attachmentCopyOf id o).elim c (·.card)
      let after := createOne card o.controller o.loc (!o.exhausted) s
      (buffNewTokens s after o.controller, tokenPlays s after o.controller)
    | _ => (s, [])
  | none => (s, [])

/-- Playing a copy of a token is a safe change. -/
theorem cloneTok_safe (s : GameState) (id : ObjId) : Safe s (cloneTok s id).1 := by
  unfold cloneTok
  split
  · split
    · exact (createOne_safe _ _ _ _ s).trans (buffNewTokens_safe _ _ _)
    · exact Safe.refl s
  · exact Safe.refl s

/-- Banish an object, and note on the banished card that `src` banished it. -/
def banishMarked (p : PlayerId) (src : ObjId) (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := banishObj p s id
  match r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none) with
  | some n => (r.1.modObj n (fun x => { x with banishedWith := some src }), r.2)
  | none => r

/-- Banishing an object, noting who did it, is a safe change. -/
theorem banishMarked_safe (p : PlayerId) (src : ObjId) (s : GameState) (id : ObjId) :
    Safe s (banishMarked p src s id).1 := by
  unfold banishMarked
  dsimp only
  split
  · rename_i n hn
    exact (sendObj_safe .banishment s id).trans (Safe.modObj _ n (fun _ => rfl) (fun _ => rfl))
  · exact sendObj_safe .banishment s id

/-- Move the card to the zone of its owner, noting that `src` did it if asked. -/
def sendMarked (p : PlayerId) (src : ObjId) (mark : Bool) (k : ZoneKind) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if mark then banishMarked p src s id
  else if k == .banishment then banishObj p s id
  else sendObj k s id

/-- Moving a card, noting who did it, is a safe change. -/
theorem sendMarked_safe (p : PlayerId) (src : ObjId) (mark : Bool) (k : ZoneKind)
    (s : GameState) (id : ObjId) : Safe s (sendMarked p src mark k s id).1 := by
  unfold sendMarked
  split
  · exact banishMarked_safe p src s id
  · split
    · exact sendObj_safe .banishment s id
    · exact sendObj_safe k s id

/-- Move every card of the sides in a zone of theirs that has the properties to another zone. -/
def applyMoveAll (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (side : Side)
    (place : Place) (fs : FilterList) (dest : Place) (mark : Bool) :
    Option (GameState × List Event) :=
  match place.zoneKind?, dest.zoneKind? with
  | some z, some k =>
    let ids := (s.players.filter (fun q => side.admitsPlayer p q s.config.mode)).flatMap (fun q =>
      (s.zone (.player q z)).filter (fun u => FilterList.holds s src env u fs == some true))
    some (applyEach (sendMarked p src mark k) s ids)
  | _, _ => none

/-- The object gains a tag. -/
def gainTagObj (name : String) (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with tagsGained := o.tagsGained ++ [name] }), [])

/-- Gaining a tag is a safe change. -/
theorem gainTagObj_safe (name : String) (s : GameState) (id : ObjId) :
    Safe s (gainTagObj name s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- An effect of the player moved the units: the events say so. -/
def movedEvents (p : PlayerId) (r : GameState × List Event) : GameState × List Event :=
  (r.1, r.2 ++ r.2.filterMap (fun e => match e with
    | .standardMoved u _ => some (Event.movedByEffect p u)
    | _ => none))

/-- The units at the Battlefield `old` are at `new` instead. -/
def relocateUnits (old new : ObjId) (s : GameState) : GameState :=
  (s.zone .battlefieldZone).foldl (fun t u =>
    if (t.obj? u).any (·.loc == some old) then t.modObj u (fun o => { o with loc := some new })
    else t) s

/-- Moving the units from one Battlefield to another is a safe change. -/
theorem relocateUnits_safe (old new : ObjId) (s : GameState) : Safe s (relocateUnits old new s) := by
  unfold relocateUnits
  suffices h : ∀ (l : List ObjId) (t : GameState), Safe t (l.foldl (fun t u =>
      if (t.obj? u).any (·.loc == some old) then t.modObj u (fun o => { o with loc := some new })
      else t) t) from h _ s
  intro l
  induction l with
  | nil => intro t; exact Safe.refl t
  | cons u l ih =>
    intro t
    simp only [List.foldl_cons]
    refine Safe.trans ?_ (ih _)
    split
    · exact Safe.modObj t u (fun _ => rfl) (fun _ => rfl)
    · exact Safe.refl t

/-- The object of the Battlefield token that replaces the Battlefield `old` that is set aside as `r`. -/
def bfToken (c : CardDef) (p : PlayerId) (old : Object) (aside : ObjId) : Object :=
  { kind := .token c.id, owner := p, controller := p, timestamp := ⟨0⟩, control := old.control,
    replaces := some aside }

/-- Replace the Battlefield `b` with the Battlefield token: `b` is set aside, the token is in its
place with the units that were there, and the control of it is the one `b` had. -/
def replaceBf (c : CardDef) (p : PlayerId) (s : GameState) (b : ObjId) : GameState × List Event :=
  match s.obj? b with
  | some o =>
    match moveObj s b (.player o.owner .banishment) with
    | some r =>
      match addObject r.1 (bfToken c p o r.2) .battlefieldZone with
      | some t => (relocateUnits b t.2 t.1, [])
      | none => (s, [])
    | none => (s, [])
  | none => (s, [])

/-- Replacing a Battlefield is a safe change. -/
theorem replaceBf_safe (c : CardDef) (p : PlayerId) (s : GameState) (b : ObjId) :
    Safe s (replaceBf c p s b).1 := by
  unfold replaceBf
  cases ho : s.obj? b with
  | none => simp only []; exact Safe.refl s
  | some o =>
    simp only []
    cases hr : moveObj s b (.player o.owner .banishment) with
    | none => simp only []; exact Safe.refl s
    | some r =>
      simp only []
      cases ht : addObject r.1 (bfToken c p o r.2) .battlefieldZone with
      | none => simp only []; exact Safe.refl s
      | some t =>
        simp only []
        exact (Safe.moveObj hr).trans ((safe_addObject rfl ht).trans (relocateUnits_safe _ _ _))

/-- The Battlefield `old` is back, as `r`, where the token `cur` was: with its control, and its units. -/
def restoreStep (cur : ObjId) (o : Object) (r : GameState × ObjId) : GameState :=
  relocateUnits cur r.2 (r.1.modObj r.2 (fun x => { x with control := o.control }))

/-- Putting a Battlefield back in place of a token is a safe change. -/
theorem restoreStep_safe (cur : ObjId) (o : Object) (r : GameState × ObjId) :
    Safe r.1 (restoreStep cur o r) :=
  (Safe.modObj r.1 r.2 (f := fun x => { x with control := o.control }) (fun _ => rfl)
    (fun _ => rfl)).trans (relocateUnits_safe _ _ _)

/-- Put the Battlefield the token `cur` replaced back in its place, and the token away. -/
def restoreBf (s : GameState) (cur : ObjId) : GameState × List Event :=
  match s.obj? cur with
  | some o =>
    match o.replaces with
    | some old =>
      match moveObj s old .battlefieldZone with
      | some r =>
        match moveObj (restoreStep cur o r) cur (.player o.owner .trash) with
        | some t => (t.1, [])
        | none => (restoreStep cur o r, [])
      | none => (s, [])
    | none => (s, [])
  | none => (s, [])

/-- Putting a replaced Battlefield back is a safe change. -/
theorem restoreBf_safe (s : GameState) (cur : ObjId) : Safe s (restoreBf s cur).1 := by
  unfold restoreBf
  cases ho : s.obj? cur with
  | none => simp only []; exact Safe.refl s
  | some o =>
    simp only []
    cases hq : o.replaces with
    | none => simp only []; exact Safe.refl s
    | some old =>
      simp only []
      cases hr : moveObj s old .battlefieldZone with
      | none => simp only []; exact Safe.refl s
      | some r =>
        simp only []
        cases ht : moveObj (restoreStep cur o r) cur (.player o.owner .trash) with
        | none => simp only []; exact (Safe.moveObj hr).trans (restoreStep_safe cur o r)
        | some t =>
          simp only []
          exact ((Safe.moveObj hr).trans (restoreStep_safe cur o r)).trans (Safe.moveObj ht)

/-- The event that says the player chose the object while the effect of `src` resolved: a choice by
a spell, or by an ability. -/
def chosenAt (s : GameState) (p : PlayerId) (src o : ObjId) : List Event :=
  if (s.cardDef? src).any (·.hasType .spell) then [Event.chosenBySpell p o]
  else [Event.chosenByAbility p o]

/-- Give an object a keyword for a while (CR 479.3). -/
def addTempKw (k : KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  (s.modObj id (fun o => { o with tempKws := o.tempKws ++ [(k, ends)] }), [])

/-- Giving a keyword for a while is a safe change. -/
theorem addTempKw_safe (k : KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (addTempKw k ends s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- Give an object several keywords for a while. -/
def addTempKws (ks : List KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  (ks.foldl (fun t k => (addTempKw k ends t id).1) s, [])

/-- Giving several keywords for a while is a safe change. -/
theorem addTempKws_safe (ks : List KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (addTempKws ks ends s id).1 := by
  unfold addTempKws
  suffices h : ∀ (l : List KeywordInst) (t : GameState),
      Safe t (l.foldl (fun t k => (addTempKw k ends t id).1) t) from h ks s
  intro l
  induction l with
  | nil => intro t; exact Safe.refl t
  | cons k l ih => intro t; exact (addTempKw_safe k ends t id).trans (ih _)

/-- The keywords an object has now: those printed on its card, and those it was given. -/
def GameState.keywordsNow (s : GameState) (id : ObjId) : List KeywordInst :=
  ((s.cardDef? id).map (·.keywords)).getD [] ++ s.grantedKws id

/-- Give an object an instance of Empowered if it is in play and below its limit (CR 442). -/
def empowerObj (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id, s.cardDef? id with
  | some o, some c =>
    if o.empowerCount < c.empowerLimit &&
        (s.inPlay.contains id ||
          (c.hasType .legend && (s.zone (.player o.owner .legendZone)).contains id)) then
      (s.modObj id (fun x => { x with empowerCount := x.empowerCount + 1 }), [.empowered p id])
    else (s, [])
  | _, _ => (s, [])

/-- Empower preserves structural invariants and physical cards. -/
theorem empowerObj_safe (p : PlayerId) (s : GameState) (id : ObjId) :
    Safe s (empowerObj p s id).1 := by
  unfold empowerObj
  split
  · split
    · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
    · exact Safe.refl s
  · exact Safe.refl s

/-- Remove an instance of Empowered (CR 443). -/
def disempowerObj (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with empowerCount := o.empowerCount - 1 }), [])

/-- Disempower preserves structural invariants and physical cards. -/
theorem disempowerObj_safe (s : GameState) (id : ObjId) :
    Safe s (disempowerObj s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- A finalized Spell resolves for its current controller (CR 420.4.a, 750). -/
def spellCompletion (s : GameState) (id : ObjId) (events : List Event) (inPlace : Bool := false) :
    List Event :=
  if (s.cardDef? id).any (·.hasType .spell) then
    let moved := events.findSome? (fun
      | .moved old next _ => if old == id then some next else none
      | _ => none)
    match (s.obj? id).filter (fun _ =>
        s.playLog.any (fun play => play.object == id && play.moment == .finalized)),
        moved <|> (if inPlace then some id else none) with
    | some o, some next => [.spellResolved o.controller next] ++
      (if o.fromHidden && o.hiddenAt.isSome then [.hiddenPlayed o.controller] else [])
    | _, _ => []
  else []

/-- Draw a specific card that was looked at and is still in the player's Main Deck. -/
def drawLookedCard (p : PlayerId) (looked : List ObjId) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if looked.contains id && (s.zone (.player p .mainDeck)).contains id then
    match moveObj s id (.player p .hand) with
    | some (moved, new) =>
      (moved.noteDraw p, [.moved id new (.player p .hand), .drew p,
        .drewGroup p (s.zone (.player p .hand)).length])
    | none => (s, [])
  else (s, [])

theorem drawLookedCard_safe (p : PlayerId) (looked : List ObjId) (s : GameState) (id : ObjId) :
    Safe s (drawLookedCard p looked s id).1 := by
  unfold drawLookedCard
  split
  · split
    · rename_i moved new found
      exact (Safe.moveObj found).trans
        ⟨fun h => h.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
          fun _ h => h.congr rfl rfl, rfl⟩
    · exact Safe.refl s
  · exact Safe.refl s

/-- The controller of an object killed by the instruction, linked across its change of zone. -/
def killedController (target : ObjId) (events : List Event) : Option PlayerId :=
  events.findSome? fun
    | .moved old next _ => if old == target then
        events.findSome? fun
          | .died id controller => if id == next then some controller else none
          | _ => none
      else none
    | _ => none

/-- The Kill itself must cause the death. A replacement may kill a permanent as its own action
(CR 370.1.a.1, 429). -/
def directKilledController (s : GameState) (target : ObjId) (events : List Event) : Option PlayerId :=
  if (s.deathSaveFor target []).isSome then none else killedController target events

/-- Resolve one of a Spell's Kill actions, noting only a Unit killed by that Spell. -/
def killSpellTarget (p : PlayerId) (before current : GameState) (target : ObjId) :
    GameState × List Event :=
  let (next, events) := killOrSaveInGroup before current target
  let credited := (current.cardDef? target).any (·.hasType .unit) &&
    (directKilledController current target events).isSome
  (next, if credited then Event.killedBySpell p :: events else events)

/-- Attribution changes the event log while retaining the result of the Kill or its replacement. -/
theorem killSpellTarget_safe (p : PlayerId) (before current : GameState) (target : ObjId) :
    Safe current (killSpellTarget p before current target).1 :=
  killOrSaveInGroup_safe before current target

/-- Do a game action that changes objects: the new state and the events. `none` if the action is
not understood yet, or what it names cannot be found. -/
def applyPrim (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) :
    Prim → Option (GameState × List Event)
  | .deal sel n =>
    if s.damageOff then some (s, []) else
    (n.evalS s p src env).bind (fun k => onSelected s p src env sel
      (fun t id => dealObj (if 0 < k then k + s.bonusOn p src id env.sourceCard else k) t id
        (some (env.effectController.getD p))))
  | .exchangeDamage a b =>
    match a.eval s p src env, b.eval s p src env with
    | some (x :: _), some (y :: _) => some (exchangeDamage s x y)
    | _, _ => some (s, [])
  | .setBaseMight sel n =>
    (n.evalS s p src env).bind (fun k => onSelected s p src env sel (setBaseMight k))
  | .heal sel n => (n.evalS s p src env).bind (fun k => onSelected s p src env sel (healOne k))
  | .kill sel =>
    -- a unit killed by a spell is noted, for what waits for that (Immortal Phoenix)
    (sel.eval s p src env).map (fun ids =>
      if (s.cardDef? src).any (·.hasType .spell) then
        let (next, events) := resolveDeathGroupWith s ids (killSpellTarget p s)
        let credit := Event.killedBySpell p
        (next, events.filter (· != credit) ++ (if events.contains credit then [credit] else []))
      else resolveDeathGroupWith s ids (killOrSaveInGroup s))
  | .ready sel => onSelected s p src env sel readyEffect
  | .exhaust sel => onSelected s p src env sel (setExhausted true)
  | .banish sel => onSelected s p src env sel (banishObj p)
  | .returnToHand sel => onSelected s p src env sel (replaceChosenHarm env (sendObj .hand))
  | .create name n place ready => applyCreate s p src env name n place ready
  | .createAt name n dest ready => applyCreateAt s p src env name n dest ready
  | .playUnitTokenAt name dest => some (playUnitTokenAt s p name dest)
  | .attach gears to => applyAttach s p src env gears to
  | .copyAttachedFrom model => onSelected s p src env model (copyAttachedUnit src)
  | .detach sel => onSelected s p src env sel detachObj
  | .double sel => onSelected s p src env sel doubleObj
  | .grantActivation sel grant => onSelected s p src env sel (grantActivationObj grant)
  | .topdeck sel => onSelected s p src env sel (sendObj .mainDeck)
  | .attachPaying gears to less => applyAttachPaying s p src env gears to less
  | .move sel .base =>
    (onSelected s p src env sel (moveByEffect (env.effectController.getD p) none)).map (movedEvents p)
  | .move sel (.at_ dsel) =>
    -- the place of the first object the destination names: a Battlefield, or where a Unit is
    match dsel.eval s p src env with
    | some (d :: _) =>
      -- a Battlefield, or the Battlefield a Unit is at; a Unit at a Base names no place yet
      match (if (s.cardDef? d).any (·.hasType .battlefield) then some d
          else (s.obj? d).bind (·.loc)) with
      | some bf =>
        (onSelected s p src env sel (moveByEffect (env.effectController.getD p) (some bf))).map
          (movedEvents p)
      | none => none
    | _ => none
  | .swapPlaces a b =>
    match a.eval s p src env, b.eval s p src env with
    | some (x :: _), some (y :: _) =>
      some (movedEvents p (swapPlaces s x y (some (env.effectController.getD p))))
    | _, _ => none
  | .stun sel => onSelected s p src env sel (fun t id => stunObj t id env)
  | .buff sel => onSelected s p src env sel buffObj
  | .empower sel => onSelected s p src env sel (empowerObj p)
  | .disempower sel => onSelected s p src env sel disempowerObj
  | .gainXP ps n =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k => (gainXPAll k s l, [])))
  | .spendXP ps n =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k => (spendXPAll k s l, [])))
  | .channel ps n extra =>
    (ps.resolve s p env).bind (fun l =>
      (n.evalS s p src env).bind (fun k =>
        (extra.evalS s p src env).map (fun x => channelAll k x s l)))
  | .recycle sel =>
    -- recycling a card that is a card (not a Rune), even in its deck, is noted
    (sel.eval s p src env).map (fun ids =>
      let r := applyEach recycleOne s ids
      (r.1, r.2 ++ (if ids.any (fun id => (s.obj? id).isSome && recycleKind s id == .mainDeck)
        then [Event.recycled p] else []) ++
        (if sel == .self then spellCompletion s src r.2 true else [])))
  -- revealing shows information: nothing changes, but the object is chosen
  | .reveal sel =>
    -- a card revealed from its owner's deck is noted: what waits for it fires (Undertitan)
    some (s, ((sel.eval s p src env).getD []).filterMap (fun id =>
      match s.obj? id with
      | some o => if (s.zone (.player o.owner .mainDeck)).contains id then
          some (Event.revealed o.owner id) else none
      | none => none))
  | .revealTop n =>
    -- the top cards of the Main Deck are revealed: what waits for them fires
    some (s, ((s.zone (.player p .mainDeck)).take n).map (fun id => Event.revealed p id))
  | .revealTopNow n =>
    some (s, ((s.zone (.player p .mainDeck)).take n).map (fun id => Event.revealed p id))
  | .drawLooked sel => onSelected s p src env sel (drawLookedCard p env.lookedCards)
  | .revealNow sel =>
    -- a card revealed from its owner's deck is noted: what waits for it fires (Undertitan)
    some (s, ((sel.eval s p src env).getD []).filterMap (fun id =>
      match s.obj? id with
      | some o => if (s.zone (.player o.owner .mainDeck)).contains id then
          some (Event.revealed o.owner id) else none
      | none => none))
  | .spendBuff sel => onSelected s p src env sel unbuffObj
  | .play sel | .playAtBase sel => onSelected s p src env sel (playFree p)
  | .banishReplay sel keep =>
    onSelected s p src env sel (fun t id => banishReplay p t id keep)
  | .playPaying sel => onSelected s p src env sel (playPaying p)
  | .playTo sel bfs =>
    match bfs.eval s p src env with
    | some (b :: _) => onSelected s p src env sel (playToOrBase p b)
    | _ => none
  | .playReduced sel less dest =>
    (less.evalS s p src env).bind (fun k =>
      match dest with
      | none => onSelected s p src env sel (playReducedOne p k none)
      | some bfs =>
        match bfs.eval s p src env with
        | some (b :: _) => onSelected s p src env sel (playReducedOne p k (some b))
        | _ => none)
  | .giveKeywords to from_ =>
    (from_.eval s p src env).bind (fun l =>
      match l with
      | f :: _ => onSelected s p src env to (addTempKws (s.keywordsNow f) .turn)
      | [] => none)
  | .bin sel => (onSelected s p src env sel (sendObj .trash)).map
    (fun r => (r.1, r.2 ++ spellCompletion s src r.2))
  | .discardCard sel => onSelected s p src env sel discardObj
  | .discardWithTypeTriggers sel links =>
    let sourceCard := env.sourceCard <|> (s.cardDef? src).map (·.id)
    onSelected s p src env sel (discardWithTypeEvents p src sourceCard links)
  | .counter sel => onSelected s p src env sel counterObj
  | .counterToHand sel => onSelected s p src env sel counterObjHand
  | .hideAt sel bfs =>
    match bfs.eval s p src env with
    | some (b :: _) => onSelected s p src env sel (hideObj b)
    | _ => none
  | .recycleTop ps =>
    (ps.resolve s p env).map (fun l => (recycleTopAll s l,
      l.filterMap (fun q =>
        if (s.zone (.player q .mainDeck)).isEmpty then none else some (Event.recycled q))))
  | .swapTop ps => (ps.resolve s p env).map (fun l => (swapTopAll s l, []))
  | .takeControl sel => onSelected s p src env sel (setController p)
  | .addBattlefield name => (s.tokenCard name).map (fun c => (addBattlefieldTok c p s, []))
  | .createAtPrev name n ready => applyCreateAtPrev s p src env name n ready
  | .cloneToken sel => onSelected s p src env sel cloneTok
  | .banishWith sel => onSelected s p src env sel (banishMarked p src)
  | .gainTag sel name => onSelected s p src env sel (gainTagObj name)
  | .replaceBattlefield sel name =>
    (s.tokenCard name).bind (fun c => onSelected s p src env sel (replaceBf c p))
  | .restoreBattlefield sel => onSelected s p src env sel restoreBf
  | .moveAll side place fs dest mark => applyMoveAll s p src env side place fs dest mark
  | .becomeCopy sel from_ =>
    match from_.eval s p src env with
    | some (c :: _) => onSelected s p src env sel (becomeCopyOf c)
    | _ => none
  | .playBanishedWith =>
    some (applyEach (playFree p) s ((s.zone (.player p .banishment)).filter (fun id =>
      (s.obj? id).any (·.banishedWith == some src) && (s.cardDef? id).any (·.hasType .unit))))
  | .returnControl sel => onSelected s p src env sel giveBack
  | .takeControlUntilLeaves sel =>
    onSelected s p src env sel (takeUntil p (some src))
  | .recall sel ex => onSelected s p src env sel (recallFx ex)
  | .win ps =>
    -- winning is reaching the Victory Score: the Cleanup that follows declares the winner
    (ps.resolve s p env).map (fun l =>
      (gainPointsAll s.victoryScore s l, []))
  | .score ps n =>
    -- a player who cannot score gets no point from the effect either (Tianna)
    (ps.resolve s p env).bind (fun l0 => (n.evalS s p src env).map (fun k =>
      let l := l0.filter (fun q => !s.cantActHere q .score src)
      (gainPointsAll k s l, if k = 0 then [] else l.map (fun q => Event.pointsGained q k))))
  | .turnEffect e =>
    -- a Spell played from hiding is played too (what waits for a spell played fires)
    some (s.addTurnFx p e, if e == .hiddenPlayed then
      Event.hiddenPlayed p :: (if (s.cardDef? src).any (·.hasType .spell) then
        [Event.played p src] else [])
      else [])
  | .playFirst fs => some (playFirstOf fs p src env s)
  | .markOn sel e => onSelected s p src env sel
      (fun t id => (t.addTurnFxOn p id (e.forCopy env.abilityCopyStamp), []))
  | .delayUntilDeath sel idx =>
    (env.sourceCard <|> (s.cardDef? src).map (·.id)).bind (fun card =>
      onSelected s p src env sel (fun t id =>
        (t.addTurnFxOn p id (.triggerOnDeath src card idx), [])))
  | .returnChampion => some (returnChampion p s)
  | .extraTurn ps =>
    (ps.resolve s p env).map (fun l => ({ s with extraTurns := s.extraTurns ++ l }, []))
  | .lookTop n => some (s, ((s.zone (.player p .mainDeck)).take n).map (Event.lookedAt p))
  | .choose sel => (sel.eval s p src env).map (fun ids => (s, ids.flatMap (chosenAt s p src)))
  | .activateConquer sel =>
    onSelected s p src env sel (fun t id => (t, [Event.conquerActivated id]))
  | .pay c =>
    -- from the Pool, or with Runes if it falls short; nothing is paid if it cannot be
    match payByRunes s p src c with
    | some r => some r
    | none => some (s, [])
  | .addEnergy ps n none =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addEnergy k) s l, [])))
  | .addUnitEnergy ps n =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addUnitEnergy k) s l, [])))
  | .addSpellEnergy ps n =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addSpellEnergy k) s l, [])))
  | .addPower ps n (some d) none =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addPower d k) s l, [])))
  | .addPower ps n none none =>
    (ps.resolve s p env).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsAddAny k s l, [])))
  | _ => none

/-- An action that is done is a safe change. -/
theorem applyPrim_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {pr : Prim}
    {r : GameState × List Event} (h : applyPrim s p src env pr = some r) : Safe s r.1 := by
  cases pr with
  | deal sel n =>
    simp only [applyPrim] at h
    by_cases hd : s.damageOff = true
    · simp only [hd, ite_true, Option.some.injEq] at h
      subst h
      exact Safe.refl s
    · simp only [hd] at h
      cases hn : n.evalS s p src env with
      | none => simp [hn] at h
      | some k =>
        simp only [hn, Option.bind_some] at h
        exact onSelected_safe (fun t id => dealObj_safe _ t id (some (env.effectController.getD p))) h
  | exchangeDamage a b =>
    simp only [applyPrim] at h
    split at h
    · rename_i x xs y ys _ _
      cases h
      exact exchangeDamage_safe s x y
    · cases h
      exact Safe.refl s
  | setBaseMight sel n =>
    simp only [applyPrim] at h
    cases hn : n.evalS s p src env with
    | none => simp [hn] at h
    | some k => exact onSelected_safe (setBaseMight_safe k) (by simpa [hn] using h)
  | heal sel n =>
    simp only [applyPrim] at h
    cases hn : n.evalS s p src env with
    | none => simp [hn] at h
    | some k =>
      simp only [hn, Option.bind_some] at h
      exact onSelected_safe (healOne_safe k) h
  | kill sel =>
    simp only [applyPrim] at h
    cases hs : sel.eval s p src env with
    | none => simp [hs] at h
    | some ids =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      rw [← h]
      split
      · exact resolveDeathGroupWith_safe s ids (killSpellTarget_safe p s)
      · exact resolveDeathGroupWith_safe s ids (killOrSaveInGroup_safe s)
  | ready sel => exact onSelected_safe readyEffect_safe h
  | exhaust sel => exact onSelected_safe (setExhausted_safe true) h
  | banish sel => exact onSelected_safe (banishObj_safe p) h
  | returnToHand sel => exact onSelected_safe (replaceChosenHarm_safe env (sendObj_safe .hand)) h
  | create name n place ready => exact applyCreate_safe h
  | createAt name n dest ready => exact applyCreateAt_safe h
  | playUnitTokenAt name dest =>
    cases h
    exact playUnitTokenAt_safe s p name dest
  | attach gears to => exact applyAttach_safe h
  | copyAttachedFrom model => exact onSelected_safe (copyAttachedUnit_safe src) h
  | attachPaying gears to less => exact applyAttachPaying_safe h
  | move sel dest =>
    cases dest with
    | base =>
      simp only [applyPrim] at h
      obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.mp h
      show Safe s r0.1
      exact onSelected_safe (moveByEffect_safe _ none) hr0
    | at_ t =>
      simp only [applyPrim] at h
      cases hd : t.eval s p src env with
      | none => simp [hd] at h
      | some l =>
        cases l with
        | nil => simp [hd] at h
        | cons d _ =>
          simp only [hd] at h
          split at h
          · obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.mp h
            show Safe s r0.1
            exact onSelected_safe (moveByEffect_safe _ _) hr0
          · simp at h
  | stun sel => exact onSelected_safe (fun t id => stunObj_safe t id env) h
  | detach sel => exact onSelected_safe detachObj_safe h
  | double sel => exact onSelected_safe doubleObj_safe h
  | grantActivation sel grant => exact onSelected_safe (grantActivationObj_safe grant) h
  | topdeck sel => exact onSelected_safe (sendObj_safe .mainDeck) h
  | buff sel => exact onSelected_safe buffObj_safe h
  | empower sel => exact onSelected_safe (empowerObj_safe p) h
  | disempower sel => exact onSelected_safe disempowerObj_safe h
  | gainXP ps n =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h]
        exact gainXPAll_safe k l s
  | spendXP ps n =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h]
        exact spendXPAll_safe k l s
  | recycle sel =>
    simp only [applyPrim] at h
    cases hs : sel.eval s p src env with
    | none => simp [hs] at h
    | some ids =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact applyEach_safe (fun t u => recycleOne_safe t u) _ _
  | reveal sel =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | drawLooked sel => exact onSelected_safe (drawLookedCard_safe p env.lookedCards) h
  | revealNow sel =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | revealTop n =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | revealTopNow n =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | spendBuff sel => exact onSelected_safe unbuffObj_safe h
  | play sel => exact onSelected_safe (playFree_safe p) h
  | playAtBase sel => exact onSelected_safe (playFree_safe p) h
  | banishReplay sel keep => exact onSelected_safe (fun t id => banishReplay_safe p t id keep) h
  | playPaying sel => exact onSelected_safe (playPaying_safe p) h
  | playTo sel bfs =>
    simp only [applyPrim] at h
    cases hb : bfs.eval s p src env with
    | none => simp [hb] at h
    | some l =>
      cases l with
      | nil => simp [hb] at h
      | cons b _ =>
        simp only [hb] at h
        exact onSelected_safe (playToOrBase_safe p b) h
  | playReduced sel less dest =>
    simp only [applyPrim] at h
    cases hk : less.evalS s p src env with
    | none => simp [hk] at h
    | some k =>
      simp only [hk, Option.bind_some] at h
      cases dest with
      | none => exact onSelected_safe (playReducedOne_safe p k none) h
      | some bfs =>
        cases hb : bfs.eval s p src env with
        | none => simp [hb] at h
        | some l =>
          cases l with
          | nil => simp [hb] at h
          | cons b _ =>
            simp only [hb] at h
            exact onSelected_safe (playReducedOne_safe p k (some b)) h
  | giveKeywords to from_ =>
    simp only [applyPrim] at h
    cases hf : from_.eval s p src env with
    | none => simp [hf] at h
    | some l =>
      cases l with
      | nil => simp [hf] at h
      | cons f _ =>
        simp only [hf, Option.bind_some] at h
        exact onSelected_safe (addTempKws_safe _ _) h
  | bin sel =>
    simp only [applyPrim, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    have hs : Safe s r.1 := onSelected_safe (sendObj_safe .trash) hr
    exact hs
  | discardCard sel => exact onSelected_safe discardObj_safe h
  | discardWithTypeTriggers sel links =>
    exact onSelected_safe (discardWithTypeEvents_safe p src _ links) h
  | counter sel => exact onSelected_safe counterObj_safe h
  | counterToHand sel => exact onSelected_safe counterObjHand_safe h
  | hideAt sel bfs =>
    simp only [applyPrim] at h
    cases hb : bfs.eval s p src env with
    | none => simp [hb] at h
    | some l =>
      cases l with
      | nil => simp [hb] at h
      | cons b _ =>
        simp only [hb] at h
        exact onSelected_safe (hideObj_safe b) h
  | recycleTop ps =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact recycleTopAll_safe l s
  | swapTop ps =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact swapTopAll_safe l s
  | becomeCopy sel from_ =>
    simp only [applyPrim] at h
    cases hf : from_.eval s p src env with
    | none => simp [hf] at h
    | some l =>
      cases l with
      | nil => simp [hf] at h
      | cons c _ =>
        simp only [hf] at h
        exact onSelected_safe (becomeCopyOf_safe c) h
  | createAtPrev name n ready =>
    simp only [applyPrim] at h
    exact applyCreateAtPrev_safe h
  | cloneToken sel => exact onSelected_safe cloneTok_safe h
  | banishWith sel => exact onSelected_safe (banishMarked_safe p src) h
  | gainTag sel name => exact onSelected_safe (gainTagObj_safe name) h
  | replaceBattlefield sel name =>
    simp only [applyPrim] at h
    cases ht : s.tokenCard name with
    | none => simp [ht] at h
    | some c =>
      simp only [ht, Option.bind_some] at h
      exact onSelected_safe (replaceBf_safe c p) h
  | restoreBattlefield sel => exact onSelected_safe restoreBf_safe h
  | moveAll side place fs dest mark =>
    simp only [applyPrim, applyMoveAll] at h
    split at h
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact applyEach_safe (fun t id => sendMarked_safe p src mark _ t id) _ _
    · simp at h
  | addBattlefield name =>
    simp only [applyPrim] at h
    cases ht : s.tokenCard name with
    | none => simp [ht] at h
    | some c =>
      simp only [ht, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact addBattlefieldTok_safe c p s
  | takeControl sel => exact onSelected_safe (setController_safe p) h
  | playBanishedWith =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact applyEach_safe (fun t u => playFree_safe p t u) _ _
  | returnControl sel => exact onSelected_safe giveBack_safe h
  | takeControlUntilLeaves sel => exact onSelected_safe (takeUntil_safe p _) h
  | «recall» sel ex => exact onSelected_safe (recallFx_safe ex) h
  | win ps =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact gainPointsAll_safe _ l s
  | score ps n =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h]
        exact gainPointsAll_safe k _ s
  | channel ps n extra =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        cases hx : extra.evalS s p src env with
        | none => simp [hl, hn, hx] at h
        | some x =>
          simp only [hl, hn, hx, Option.bind_some, Option.map_some, Option.some.injEq] at h
          rw [← h]
          exact channelAll_safe k x l s
  | playFirst fs =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact playFirstOf_safe fs p src env s
  | extraTurn ps =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p env with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
        fun _ hown => hown.congr rfl rfl, rfl⟩
  | lookTop n =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact Safe.refl s
  | choose sel =>
    simp only [applyPrim] at h
    cases hs : sel.eval s p src env with
    | none => simp [hs] at h
    | some ids =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact Safe.refl s
  | returnChampion =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact returnChampion_safe p s
  | swapPlaces a b =>
    simp only [applyPrim] at h
    cases ha : a.eval s p src env with
    | none => simp [ha] at h
    | some la =>
      cases lb : b.eval s p src env with
      | none => simp [ha, lb] at h
      | some lb' =>
        cases la with
        | nil => simp [ha, lb] at h
        | cons x _ =>
          cases lb' with
          | nil => simp [ha, lb] at h
          | cons y _ =>
            simp only [ha, lb, Option.some.injEq] at h
            rw [← h]
            exact swapPlaces_safe s x y _
  | activateConquer sel =>
    simp only [applyPrim] at h
    exact onSelected_safe (fun t id => Safe.refl t) h
  | markOn sel e =>
    simp only [applyPrim] at h
    exact onSelected_safe (fun t id => addTurnFxOn_safe t p id (e.forCopy env.abilityCopyStamp)) h
  | delayUntilDeath sel idx =>
    simp only [applyPrim, Option.bind_eq_some_iff] at h
    obtain ⟨card, -, h⟩ := h
    exact onSelected_safe (fun t id => addTurnFxOn_safe t p id (.triggerOnDeath src card idx)) h
  | turnEffect e =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact addTurnFx_safe s p e
  | addEnergy ps n only =>
    cases only with
    | some a => simp [applyPrim] at h
    | none =>
      simp only [applyPrim] at h
      cases hl : ps.resolve s p env with
      | none => simp [hl] at h
      | some l =>
        cases hn : n.evalS s p src env with
        | none => simp [hl, hn] at h
        | some k =>
          simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
          rw [← h]
          exact poolsMap_safe _ l s
  | addUnitEnergy ps n | addSpellEnergy ps n =>
    simp only [applyPrim, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨l, -, k, -, rfl⟩ := h
    exact poolsMap_safe _ l s
  | addPower ps n d only =>
    cases d with
    | none =>
      cases only with
      | some a => simp [applyPrim] at h
      | none =>
        simp only [applyPrim] at h
        cases hl : ps.resolve s p env with
        | none => simp [hl] at h
        | some l =>
          cases hn : n.evalS s p src env with
          | none => simp [hl, hn] at h
          | some k =>
            simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
            rw [← h]
            exact poolsAddAny_safe _ l s
    | some dom =>
      cases only with
      | some a => simp [applyPrim] at h
      | none =>
        simp only [applyPrim] at h
        cases hl : ps.resolve s p env with
        | none => simp [hl] at h
        | some l =>
          cases hn : n.evalS s p src env with
          | none => simp [hl, hn] at h
          | some k =>
            simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
            rw [← h]
            exact poolsMap_safe _ l s
  | pay c =>
    simp only [applyPrim] at h
    cases hp : payByRunes s p src c with
    | none => simp only [hp, Option.some.injEq] at h; subst h; exact Safe.refl s
    | some x =>
      simp only [hp, Option.some.injEq] at h
      subst h
      exact payByRunes_safe hp
  | _ => simp [applyPrim] at h

/-- When a lasting effect ends, if the model has a way to end it. -/
def Duration.endPoint? : Duration → Option EndPoint
  | .thisTurn => some .turn
  | .thisCombat => some .combat
  | .permanent => some .never
  | _ => none

/-- The Might an object has for the choice of "to a minimum": the Might the rules read now, with
the lasting changes, the buff, the Equipment and the passive abilities (CR 479.4). -/
def GameState.mightBase (s : GameState) (id : ObjId) : Int :=
  (s.mightNow id).getD 0

/-- Take `k` Might from an object for a while, but not below `floor`: the change is as much as
the Might has above the floor, at most `k` (CR 475). -/
def addMightFloor (k floor : Nat) (ends : EndPoint) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  addMightMod ⟨-((Nat.min k (s.mightBase id - floor).toNat : Nat) : Int), ends⟩ s id

/-- Taking Might to a minimum is a safe change. -/
theorem addMightFloor_safe (k floor : Nat) (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (addMightFloor k floor ends s id).1 :=
  addMightMod_safe _ s id

/-- Give negative Might, applying replacements from the chosen Unit and the effect's controller
while keeping any minimum on the reduction (CR 370). -/
def reduceMight (p : PlayerId) (env : Env) (n : Nat) (floor : Option Nat) (ends : EndPoint)
    (s : GameState) (id : ObjId) : GameState × List Event :=
  if n == 0 || floor.any (fun minimum => decide (s.mightBase id ≤ (minimum : Int))) then (s, [])
  else replaceChosenHarm env (fun t target =>
    let extra := if env.targetObjs.contains target && (t.cardDef? target).any (·.hasType .unit) then
      ((t.controlledMods (env.effectController.getD p)).filterMap (fun
        | .targetMightPenalty k => some k
        | _ => none)).sum
      else 0
    match floor with
    | some fl => addMightFloor (n + extra) fl ends t target
    | none => addMightMod ⟨-((n + extra : Nat) : Int), ends⟩ t target) s id

/-- Giving negative Might, including replacement effects, preserves safety. -/
theorem reduceMight_safe (p : PlayerId) (env : Env) (n : Nat) (floor : Option Nat)
    (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (reduceMight p env n floor ends s id).1 := by
  unfold reduceMight
  split
  · exact Safe.refl s
  · apply replaceChosenHarm_safe
    intro t target
    cases floor
    · exact addMightMod_safe _ t target
    · exact addMightFloor_safe _ _ _ t target

/-- Grant Flow for a Spell's base cost before any play-time adjustments (CR 356.1, 829). -/
def addFlowAtBaseCost (ends : EndPoint) (s : GameState) (id : ObjId) : GameState × List Event :=
  match (s.cardDef? id).bind (fun d => if d.hasType .spell then d.cost else none) with
  | some cost => addTempKw ⟨.flow, .cost cost⟩ ends s id
  | none => (s, [])

/-- Granting Flow at the base cost preserves the structural and ownership invariants. -/
theorem addFlowAtBaseCost_safe (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (addFlowAtBaseCost ends s id).1 := by
  unfold addFlowAtBaseCost
  split
  · exact addTempKw_safe _ _ _ _
  · exact Safe.refl s

/-- Grant a temporary change to the selected objects. -/
def applyGrant (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (m : StaticMod) (d : Duration) : Option (GameState × List Event) :=
  let minus (a : Amount) (floor : Option Nat) : Option (GameState × List Event) :=
    d.endPoint?.bind (fun ends => (a.evalS s p src env).bind (fun k =>
      onSelected s p src env sel (reduceMight p env k floor ends)))
  match m with
  | .mightPlus .it a =>
    d.endPoint?.bind (fun ends => (a.evalS s p src env).bind (fun k =>
      onSelected s p src env sel (addMightMod ⟨(k : Int), ends⟩)))
  | .mightMinus .it a => minus a none
  | .mightMinusMin .it a fl => minus a (some fl)
  | .keyword .it k => d.endPoint?.bind (fun ends => onSelected s p src env sel (addTempKw k ends))
  | .flowAtBaseCost => d.endPoint?.bind (fun ends => onSelected s p src env sel (addFlowAtBaseCost ends))
  | _ => none

/-- A lasting change that is made is a safe change. -/
theorem applyGrant_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {sel : Selector}
    {m : StaticMod} {d : Duration} {r : GameState × List Event}
    (h : applyGrant s p src env sel m d = some r) : Safe s r.1 := by
  unfold applyGrant at h
  split at h
  · simp only at h
    cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      cases hk : (‹Amount›).evalS s p src env with
      | none => simp [hd, hk] at h
      | some k =>
        simp only [hd, hk, Option.bind_some] at h
        exact onSelected_safe (addMightMod_safe _) h
  · simp only at h
    cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      cases hk : (‹Amount›).evalS s p src env with
      | none => simp [hd, hk] at h
      | some k =>
        simp only [hd, hk, Option.bind_some] at h
        exact onSelected_safe (reduceMight_safe p env k none ends) h
  · simp only at h
    cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      cases hk : (‹Amount›).evalS s p src env with
      | none => simp [hd, hk] at h
      | some k =>
        simp only [hd, hk, Option.bind_some] at h
        exact onSelected_safe (reduceMight_safe p env k (some _) ends) h
  · cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      simp only [hd, Option.bind_some] at h
      exact onSelected_safe (addTempKw_safe _ _) h
  · cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      simp only [hd, Option.bind_some] at h
      exact onSelected_safe (addFlowAtBaseCost_safe _) h
  · simp at h

/-- The selector of a primitive that is chosen while the effect resolves, if it has one. -/
def Prim.pickSel? : Prim → Option Selector
  | .createAt _ _ dest _ => some dest
  | .detach s => some s
  | .copyAttachedFrom s => some s
  | .double s => some s
  | .topdeck s => some s
  | .deal s _ => some s
  | .setBaseMight s _ => some s
  | .heal s _ => some s
  | .kill s => some s
  | .ready s => some s
  | .exhaust s => some s
  | .banish s => some s
  | .returnToHand s => some s
  | .stun s => some s
  | .buff s => some s
  | .empower s => some s
  | .disempower s => some s
  | .recycle s => some s
  | .spendBuff s => some s
  | .bin s => some s
  | .discardCard s | .discardWithTypeTriggers s _ => some s
  | .play s | .playAtBase s => some s
  | .banishReplay s _ => some s
  | .playPaying s => some s
  | .playReduced s _ _ => some s
  | .castInline s => some s
  | .markOn s _ => some s
  | .delayUntilDeath s _ => some s
  | .playTo s _ => some s
  | .banishWith s => some s
  | .counterToHand s => some s
  | .replaceBattlefield s _ => some s
  | .reveal s => some s
  | .revealNow s | .drawLooked s => some s
  | .move s d =>
    match s, d with
    | .pick .one _ _ _, _ => some s
    | _, .at_ (.pick .one side place fs) => some (.pick .one side place fs)
    | _, _ => none
  | _ => none

/-- The primitive with its selector replaced. -/
def Prim.withSel (p : Prim) (sel : Selector) : Prim :=
  match p with
  | .createAt name count _ entersReady => .createAt name count sel entersReady
  | .copyAttachedFrom _ => .copyAttachedFrom sel
  | .deal _ n => .deal sel n
  | .setBaseMight _ n => .setBaseMight sel n
  | .heal _ n => .heal sel n
  | .detach _ => .detach sel
  | .double _ => .double sel
  | .topdeck _ => .topdeck sel
  | .kill _ => .kill sel
  | .ready _ => .ready sel
  | .exhaust _ => .exhaust sel
  | .banish _ => .banish sel
  | .returnToHand _ => .returnToHand sel
  | .stun _ => .stun sel
  | .buff _ => .buff sel
  | .empower _ => .empower sel
  | .disempower _ => .disempower sel
  | .recycle _ => .recycle sel
  | .spendBuff _ => .spendBuff sel
  | .bin _ => .bin sel
  | .discardCard _ => .discardCard sel
  | .discardWithTypeTriggers _ links => .discardWithTypeTriggers sel links
  | .play _ => .play sel
  | .playAtBase _ => .playAtBase sel
  | .banishReplay _ keep => .banishReplay sel keep
  | .playPaying _ => .playPaying sel
  | .playReduced _ l d => .playReduced sel l d
  | .castInline _ => .castInline sel
  | .markOn _ e => .markOn sel e
  | .delayUntilDeath _ idx => .delayUntilDeath sel idx
  | .playTo _ bf => .playTo sel bf
  | .banishWith _ => .banishWith sel
  | .counterToHand _ => .counterToHand sel
  | .replaceBattlefield _ n => .replaceBattlefield sel n
  | .reveal _ => .reveal sel
  | .revealNow _ => .revealNow sel
  | .drawLooked _ => .drawLooked sel
  | .move s d =>
    match s, d with
    | .pick .one _ _ _, _ => .move sel d
    | _, .at_ (.pick .one _ _ _) => .move s (.at_ sel)
    | _, _ => .move s d
  | q => q

/-- The effect names one object to choose while it resolves ("kill a gear", "stun a unit"): the
selector that does it. -/
def Effect.pickSel? : Effect → Option Selector
  | .doThen (.prim (.banish (.pick .one side place fs))) _
  | .doThen (.prim (.disempower (.pick .one side place fs))) _
  | .doThen (.prim (.exhaust (.pick .one side place fs))) _ =>
    some (.pick .one side place fs)
  | .prim p =>
    match p.pickSel? with
    | some (.pick .one side place fs) => some (.pick .one side place fs)
    | _ => none
  | .grant (.pick .one side place fs) _ _ => some (.pick .one side place fs)
  | .fillSlot _ (.pick .one side place fs) => some (.pick .one side place fs)
  | .chooseObject side place fs _ => some (.pick .one side place fs)
  | _ => none

/-- The effect with the chosen object, named by `pickVar`, in place of the selector. -/
def Effect.withPick : Effect → Effect
  | .doThen (.prim a) b => .doThen (.prim (a.withSel (.var pickVar))) b
  | .prim p => .prim (p.withSel (.var pickVar))
  | .grant (.pick .one _ _ _) m d => .grant (.var pickVar) m d
  | .fillSlot i _ => .fillFromPick i
  | .chooseObject _ _ _ body => .seq (.cons body .nil)
  | e => e

/-- Whether the object is picked for the cost of a linked instruction (CR 355.10.c.1). -/
def Effect.isLinkedCost : Effect → Bool
  | .doThen (.prim (.banish _)) _ | .doThen (.prim (.disempower _)) _
  | .doThen (.prim (.spendBuff _)) _ | .doThen (.prim (.exhaust _)) _ => true
  | _ => false

/-- Picks for costs or by multiple players do not fire target effects (CR 355.10.c.1, 355.10.e).
Keeping original targets does not choose them again (CR 355.11.b). Movement destinations only
name the location (CR 355.18). -/
def Effect.pickTargets (e : Effect) : Bool :=
  match e with
  | .retainTargetSet _ | .collectOwnPicks .. | .doThen (.prim (.move ..)) _ |
      .prim (.castInline _) | .prim (.createAt ..) | .recordRuneRecycle .. |
      .addReservedLegendPicked | .playOfferedCard .. | .recordBanishReplay .. => false
  | _ => !e.isLinkedCost

/-- A resolution pick in a private or secret zone is not a target (CR 355.10.a). -/
def Effect.pickIsTarget (e : Effect) (s : GameState) (id : ObjId) : Bool :=
  e.pickTargets && match s.locate id with
    | some (.player _ .hand) | some (.player _ .mainDeck) | some (.player _ .runeDeck) => false
    | _ => true

/-- Emit the choice event for a new target picked during resolution. -/
def Effect.pickEvents (e : Effect) (s : GameState) (p : PlayerId) (src id : ObjId) : List Event :=
  if e.pickIsTarget s id then chosenAt s p src id else []

/-- Move a playable Spell to the Chain and continue the parent effect (CR 354.3, 420.3.c). -/
def castLimitedStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (card : ObjId)
    (price : EffectPlayPrice) (exit : LimitedSpellExit) (es : EffectList) (funding : EffectAddPolicy) :
    GameState × List Frame × List Event :=
  let next := [Frame.run p src env es]
  if (limitedSpellChoices s p card price funding).isEmpty then (s, next, [.skipped src]) else
    match queueLimitedSpell s p card price exit with
    | some (t, item) => (t, next, [.moved card item .chain])
    | none => (s, next, [.skipped src])

/-- Starting a limited play preserves the game invariants. -/
theorem castLimitedStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (card : ObjId) (price : EffectPlayPrice) (exit : LimitedSpellExit) (es : EffectList)
    (funding : EffectAddPolicy) : Safe s (castLimitedStep s p src env card price exit es funding).1 := by
  unfold castLimitedStep
  dsimp only
  split
  · exact Safe.refl s
  · split
    · exact queueLimitedSpell_safe (by assumption)
    · exact Safe.refl s

/-- Starting a limited play only schedules the remaining work of the parent effect. -/
theorem castLimitedStep_mem {s : GameState} {p : PlayerId} {src card : ObjId} {env : Env}
    {price : EffectPlayPrice} {exit : LimitedSpellExit} {es : EffectList} {funding : EffectAddPolicy} {f : Frame}
    (hf : f ∈ (castLimitedStep s p src env card price exit es funding).2.1) : f.isPlay = true := by
  unfold castLimitedStep at hf
  dsimp only at hf
  split at hf
  · obtain rfl := List.mem_singleton.mp hf
    rfl
  · split at hf <;> obtain rfl := List.mem_singleton.mp hf <;> rfl

/-- Queue a Trash Spell ignoring its base Energy (Kai'Sa, Fizz). -/
def castInlineStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (es : EffectList) (funding : EffectAddPolicy) : GameState × List Frame × List Event :=
  match sel.eval s p src env with
  | some (id :: _) => castLimitedStep s p src env id .ignoreEnergy .recycle es funding
  | _ => (s, [.run p src env es], [.skipped src])

/-- Queuing a Trash Spell preserves the game invariants. -/
theorem castInlineStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (sel : Selector) (es : EffectList) (funding : EffectAddPolicy) :
    Safe s (castInlineStep s p src env sel es funding).1 := by
  unfold castInlineStep
  split
  · exact castLimitedStep_safe _ _ _ _ _ _ _ _ _
  · exact Safe.refl s

/-- The queued play continues with the parent Spell's remaining work. -/
theorem castInlineStep_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {es : EffectList} {funding : EffectAddPolicy} {f : Frame}
    (hf : f ∈ (castInlineStep s p src env sel es funding).2.1) : f.isPlay = true := by
  unfold castInlineStep at hf
  split at hf
  · exact castLimitedStep_mem hf
  · obtain rfl := List.mem_singleton.mp hf
    rfl

/-- Undo the queued play. Returning to the original zone retains its order among the cards
that were there before it and are still present. Tentative resource activations are discarded. -/
def cancelLimitedStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (card : ObjId)
    (es : EffectList) : GameState × List Frame × List Event :=
  let next := Frame.run p src env es
  match s.pendingSpell card with
  | none => (s, [next], [])
  | some play =>
    let index := play.preceding.countP (fun id => (s.zone play.origin).contains id)
    match moveObj s card play.origin (.atIndex index) with
    | some (t, restored) => (t, afterItem t ++ [next], [.moved card restored play.origin])
    | none => (s, [next], [])

/-- Returning a Spell to its original zone preserves the game invariants. -/
theorem cancelLimitedStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (card : ObjId) (es : EffectList) : Safe s (cancelLimitedStep s p src env card es).1 := by
  unfold cancelLimitedStep
  split
  · exact Safe.refl s
  · dsimp only
    split
    · exact Safe.moveObj (by assumption)
    · exact Safe.refl s

/-- The continuation after cancellation consists of play frames. -/
theorem cancelLimitedStep_mem {s : GameState} {p : PlayerId} {src card : ObjId} {env : Env}
    {es : EffectList} {f : Frame} (hf : f ∈ (cancelLimitedStep s p src env card es).2.1) :
    f.isPlay = true := by
  unfold cancelLimitedStep at hf
  split at hf
  · obtain rfl := List.mem_singleton.mp hf
    rfl
  · dsimp only at hf
    split at hf
    · rcases List.mem_append.mp hf with ha | hn
      · exact afterItem_mem ha
      · obtain rfl := List.mem_singleton.mp hn
        rfl
    · obtain rfl := List.mem_singleton.mp hf
      rfl

/-- Offer legal targets, modes, and costs once the parent effect is finished. -/
def finalizeLimitedStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (card : ObjId)
    (es : EffectList) (funding : EffectAddPolicy) : GameState × List Frame × List Event :=
  match s.pendingSpell card with
  | none => (s, [.run p src env es], [])
  | some play =>
    match limitedSpellChoices s p card play.price funding with
    | [] => cancelLimitedStep s p src env card es
    | plans =>
      let options := plans.map (fun (plan, hasAdds) =>
        if hasAdds then Effect.fundLimitedSpell card plan [] else .finishLimitedSpell card plan [])
      (s, [.run p src env (.cons (.eitherOf (EffectList.ofList options)) es)], [])

/-- Offering finalization or returning a rejected play preserves the game invariants. -/
theorem finalizeLimitedStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (card : ObjId) (es : EffectList) (funding : EffectAddPolicy) :
    Safe s (finalizeLimitedStep s p src env card es funding).1 := by
  unfold finalizeLimitedStep
  split
  · exact Safe.refl s
  · split
    · exact cancelLimitedStep_safe s p src env card es
    · exact Safe.refl s

/-- The continuation from a queued finalization consists of play frames. -/
theorem finalizeLimitedStep_mem {s : GameState} {p : PlayerId} {src card : ObjId} {env : Env}
    {es : EffectList} {funding : EffectAddPolicy} {f : Frame}
    (hf : f ∈ (finalizeLimitedStep s p src env card es funding).2.1) : f.isPlay = true := by
  unfold finalizeLimitedStep at hf
  split at hf
  · obtain rfl := List.mem_singleton.mp hf
    rfl
  · split at hf
    · exact cancelLimitedStep_mem hf
    · obtain rfl := List.mem_singleton.mp hf
      rfl

/-- Offer another Add, payment from the projected Pool, or cancellation. -/
def fundLimitedOptions (s : GameState) (p : PlayerId) (card : ObjId) (plan : EffectSpellPlay)
    (adds : List EffectAdd) (funding : EffectAddPolicy) : List Effect := Id.run do
  let cancel := Effect.cancelLimitedSpell card
  let some (t, _) := funding.applyAll s p adds | return [cancel]
  let some play := t.pendingSpell card | return [cancel]
  let pay := if (effectSpellPoolPayment t p card play.price plan).isSome then
    [Effect.finishLimitedSpell card plan adds] else []
  let activate := (effectSpellAddChoices t p card play.price plan funding).map (fun a =>
    Effect.fundLimitedSpell card plan (adds ++ [a]))
  return pay ++ activate ++ [cancel]

/-- Commit the selected Adds and finalize the Spell together, allowing Reactions afterwards. -/
def commitLimitedSpell (s : GameState) (p : PlayerId) (card : ObjId) (plan : EffectSpellPlay)
    (adds : List EffectAdd) (funding : EffectAddPolicy) : Option (GameState × List Event) := do
  let (funded, events) ← funding.applyAll s p adds
  let play ← funded.pendingSpell card
  let pool ← effectSpellPoolPayment funded p card play.price plan
  let paid := funded.setPoolFor p card pool
  let discarded := payDiscards p paid plan.discard.toList
  let discardPaid := !discarded.2.isEmpty
  let chosen := plan.pick.optionalCosts.getD (false, 0)
  let mark := { paid.playMark p card ⟨plan.cost.energy, []⟩ (pick := plan.pick) with
    spellPick := plan.pick, paid := chosen.1 || discardPaid, extraPaid := chosen.2,
    fromHand := match play.origin with | .player _ .hand => true | _ => false }
  let final := discarded.1.modObj card (fun o =>
    { o.withPlay plan.targets mark with pendingSpellPlay := none, discardPaid })
  let targetCost := castPayOnTarget s card plan.targets (final, []) (some card)
  let completed := paySpellCosts targetCost.1 card
  some (completed.1, events ++ paid.showOffEvents p plan.pick.showOffObject ++ discarded.2 ++
    targetCost.2 ++ completed.2 ++ [.played p card] ++ plan.targets.map (.chosenBySpell p))

/-- Committing a queued Spell preserves the game invariants. -/
theorem commitLimitedSpell_safe {s : GameState} {p : PlayerId} {card : ObjId} {plan : EffectSpellPlay}
    {adds : List EffectAdd} {funding : EffectAddPolicy} {r : GameState × List Event}
    (h : commitLimitedSpell s p card plan adds funding = some r) : Safe s r.1 := by
  unfold commitLimitedSpell at h
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨⟨t, events⟩, ht, play, -, pool, -, hr⟩ := h
  rw [← hr]
  have hfunded := (funding.safe (r := (t, events)) ht).trans (setPoolFor_safe t p card pool)
  refine hfunded.trans ((payDiscards_safe p plan.discard.toList _).trans ?_)
  refine Safe.trans ?_ (paySpellCosts_safe _ card)
  refine Safe.trans ?_ (castPayOnTarget_safe s card plan.targets _ (some card))
  exact Safe.modObj _ card (fun _ => rfl) (fun _ => rfl)

/-- A Spell played for a reduced cost (Void Rush). If the choice is a Unit or Gear, it
continues its own play process. -/
def castReducedStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (less : Amount) (dest : Option Selector) (es : EffectList) (funding : EffectAddPolicy) :
    Option (GameState × List Frame × List Event) :=
  match dest, sel.eval s p src env with
  | none, some (id :: _) =>
    if (s.cardDef? id).any (·.hasType .spell) then
      let amount := (less.evalS s p src env).getD 0
      some (castLimitedStep s p src env id (.reduceEnergy amount) .normal es funding)
    else none
  | _, _ => none

/-- Starting a reduced-cost Spell preserves the game invariants. -/
theorem castReducedStep_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {less : Amount} {dest : Option Selector} {es : EffectList}
    {funding : EffectAddPolicy} {r : GameState × List Frame × List Event}
    (h : castReducedStep s p src env sel less dest es funding = some r) : Safe s r.1 := by
  unfold castReducedStep at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h
      exact castLimitedStep_safe _ _ _ _ _ _ _ _ _
    · contradiction
  · contradiction

/-- Starting a reduced-cost Spell continues the parent effect. -/
theorem castReducedStep_frames {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {less : Amount} {dest : Option Selector} {es : EffectList}
    {funding : EffectAddPolicy} {r : GameState × List Frame × List Event}
    (h : castReducedStep s p src env sel less dest es funding = some r) {f : Frame}
    (hf : f ∈ r.2.1) : f.isPlay = true := by
  unfold castReducedStep at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h
      exact castLimitedStep_mem hf
    · contradiction
  · contradiction

/-- Play a Spell ignoring its base price. A separate object cost is still chosen and paid during
finalization (CR 356.1, 420.3). A choice-free Spell without such a cost resolves inline. -/
def playSpellStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (es : EffectList) (funding : EffectAddPolicy) : Option (GameState × List Frame × List Event) :=
  match sel.eval s p src env with
  | some (id :: _) =>
    if (s.cardDef? id).any (·.spellObjectCost.isSome) then
      some (castLimitedStep s p src env id .ignoreBase .normal es funding)
    else match (s.cardDef? id).bind (fun d => (d.spellEffect.bind (·.forPick .plain)).map (fun e => (d, e))) with
    | some (d, e) =>
      if d.hasType .spell && e.choices.isEmpty && e.playerTarget.isNone && !s.blocksPlay p id d then
        (moveObj s id .chain).map (fun r =>
          ((r.1.modObj r.2 (fun o =>
              { Object.withPlay [] (s.freeMark p id) o with controller := p })),
            [.run p r.2 {} (.cons e.body (.cons (.prim (.bin .self)) .nil)), .cleanup,
              .run p src env es],
            [Event.moved id r.2 .chain, Event.played p r.2]))
      else none
    | none => none
  | _ => none

/-- Playing a Spell for free is a safe change of the state. -/
theorem playSpellStep_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {es : EffectList} {funding : EffectAddPolicy}
    {r : GameState × List Frame × List Event}
    (h : playSpellStep s p src env sel es funding = some r) : Safe s r.1 := by
  unfold playSpellStep at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h
      exact castLimitedStep_safe _ _ _ _ _ _ _ _ _
    · split at h
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨s2, id'⟩, hm, rfl⟩ := h
          exact (Safe.moveObj hm).trans
            (Safe.modObj s2 id' (fun _ => rfl) (fun _ => rfl))
        · simp at h
      · simp at h
  · simp at h

/-- The frames that playing a Spell for free leaves are frames of the Spell or of the rest. -/
theorem playSpellStep_frames {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {sel : Selector} {es : EffectList} {funding : EffectAddPolicy}
    {r : GameState × List Frame × List Event}
    (h : playSpellStep s p src env sel es funding = some r) {f : Frame} (hf : f ∈ r.2.1) :
    f.isPlay = true := by
  unfold playSpellStep at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h
      exact castLimitedStep_mem hf
    · split at h
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨s2, id'⟩, hm, rfl⟩ := h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl | rfl <;> rfl
        · simp at h
      · simp at h
  · simp at h

/-- The player would reveal a card from a Main Deck and has a passive
ability that says to look at the top card first (Void Hatchling). -/
def GameState.lookFirst (s : GameState) (p : PlayerId) (env : Env) (sel : Selector) : Bool :=
  (match sel with
    | .var v =>
      match env.lookup v with
      | some (.obj o) =>
        (s.obj? o).any (fun x => (s.zone (.player x.owner .mainDeck)).contains o)
      | _ => false
    | _ => false) &&
    s.passiveSources.any (fun g => (s.obj? g).any (·.controller == p) &&
      (s.activeMods g).contains .lookBeforeReveal)

/-- Spend exactly the resources selected for an instruction (CR 445.1). -/
def spendResolutionPayment (s : GameState) (p : PlayerId) (src : ObjId) (cost : Cost)
    (gearPower : Bool := true) :
    Option RunePool :=
  s.spendSymbols p cost (gearPower && (s.cardDef? src).any (·.hasType .gear))

/-- Distinct ways of paying a resource instruction from the Pool (CR 445.1). -/
def resolutionPayments (s : GameState) (p : PlayerId) (src : ObjId) (cost : Cost)
    (gearPower : Bool := true) :
    List (Cost × RunePool) :=
  let own := ((s.cardDef? src).map (·.domains)).getD []
  s.symbolPayments p cost own (gearPower && (s.cardDef? src).any (·.hasType .gear))

mutual

/-- Whether a branch of a choice can be chosen: a branch that is a condition and nothing else is
chosen only while the condition holds ("choose one that hasn't been chosen"). -/
def Effect.viable (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) : Effect → Bool
  | .ifThen c _ .nop => c.eval s p src env == some true
  | .eitherOf es => EffectList.anyViable s p src env es
  | .payThen cost _ gearPower => !(resolutionPayments s p src cost gearPower).isEmpty
  | _ => true

/-- Whether some branch of a choice can be chosen. -/
def EffectList.anyViable (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) :
    EffectList → Bool
  | .nil => false
  | .cons e rest => Effect.viable s p src env e || EffectList.anyViable s p src env rest

end

/-- The player may answer the choice between the effects `a` and `b` with `yes` (the first) or not
(the others): the branch must be one that can be chosen, unless none can. -/
def eitherOk (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (a b : Effect)
    (yes : Bool) : Bool :=
  let va := a.viable s p src env
  let vb := b.viable s p src env
  (if yes then va else vb) || (!va && !vb)

/-- Capture the Unit cards actually put in the Trash by a linked Burn instruction. -/
def linkedBurnEvents (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (idx : Nat)
    (moves : List Event) : List Event :=
  let sourceCard := env.sourceCard <|> (s.cardDef? src).map (·.id)
  match sourceCard with
  | none => []
  | some card => moves.filterMap (fun
    | .moved _ burned (.player _ .trash) => do
      let d ← s.cardDef? burned
      if d.hasType .unit then
        some (.burnedUnitFor p src card idx burned (d.might.getD 0).toNat)
      else none
    | _ => none)

/-- Move the available top cards to the Trash for a Burn instruction or cost (CR 441). -/
def burnTop (s : GameState) (p : PlayerId) (count : Nat) : GameState × List Event :=
  applyEach (sendObj .trash) s ((s.zone (.player p .mainDeck)).take count)

/-- Burn cards for the first player and schedule the others with the same count. An exhausted
deck is refilled through the ordinary Burn Out decisions before the remainder is burned
(CR 432.1.b, 441.4). -/
def burnEffect (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (who : PlayerSel)
    (n : Amount) (es : EffectList) (unitTrigger : Option Nat := none) :
    GameState × List Frame × List Event :=
  match who.resolve s p env, n.evalS s p src env with
  | some (q :: qs), some count =>
    let available := (s.zone (.player q .mainDeck)).length
    let r := burnTop s q count
    let burnFor (pl : PlayerId) (k : Nat) :=
      let burn := match unitTrigger with
        | some idx => Prim.burnWithUnitTrigger (.const k) idx
        | none => Prim.burn .you (.const k)
      Frame.run pl src env (.cons (.prim burn) .nil)
    let rest := qs.map (fun pl => burnFor pl count) ++ [.run p src env es]
    let next :=
      if available < count then
        .chanceBurnOut q :: burnFor q (count - available) :: rest
      else rest
    let triggers := unitTrigger.toList.flatMap (fun idx => linkedBurnEvents r.1 q src env idx r.2)
    (r.1, next, r.2 ++ triggers)
  | some [], some _ => (s, [.run p src env es], [])
  | _, _ => (s, [.run p src env es], [.skipped src])

/-- Burning cards and scheduling Burn Out preserves the structural invariants. -/
theorem burnEffect_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (who : PlayerSel) (n : Amount) (es : EffectList) (link : Option Nat) :
    Safe s (burnEffect s p src env who n es link).1 := by
  unfold burnEffect
  split
  · exact applyEach_safe (sendObj_safe .trash) _ _
  · exact Safe.refl s
  · exact Safe.refl s

/-- Execute an instruction whose follow-up requires that the first action happened
(CR 359.3.e.14.b). -/
def linkedAction (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (a : Prim) :
    GameState × Bool × List Event :=
  match applyPrim s p src env a with
  | none => (s, false, [])
  | some r =>
    let done := match a with
      | .banish _ => r.2.any (fun
        | .moved _ _ (.player _ .banishment) => true
        | _ => false)
      | .disempower sel => ((sel.eval s p src env).getD []).any (fun id =>
        ((r.1.obj? id).map (·.empowerCount)).getD 0 <
          ((s.obj? id).map (·.empowerCount)).getD 0)
      | .exhaust _ => r.2.any (fun | .exhausted _ => true | _ => false)
      | .spendBuff _ => r.2.any (fun | .buffSpent _ => true | _ => false)
      | .move .. => r.2.any (fun | .standardMoved _ _ => true | _ => false)
      | _ => false
    (r.1, done, r.2)

/-- A linked action preserves the structural invariants. -/
theorem linkedAction_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (a : Prim) :
    Safe s (linkedAction s p src env a).1 := by
  unfold linkedAction
  split
  · exact Safe.refl s
  · rename_i r h
    exact applyPrim_safe h

/-- Prepare an effect Move and inspect its actual arrivals before committing.
Each Battlefield charges once, and the mover can decline the fee (CR 204.4, 412, 447).
Prevented moves and corrective Recalls create no charge. -/
def moveEffectStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (a : Prim)
    (afterMove : Effect) (es : EffectList) (feePaid : Bool := false) :
    GameState × List Frame × List Event :=
  match applyPrim s p src env a with
  | none => (s, [Frame.run p src env es], if afterMove == .nop then [.skipped src] else [])
  | some (next, events) =>
    let fields := events.filterMap (fun
      | .standardMoved id field => if (next.cardDef? id).any (·.hasType .unit) then field else none
      | _ => none)
    let fee := s.movementFee p fields
    if !feePaid && fee.total != 0 then
      let accept := Effect.payThen fee (.moveAfterFee a afterMove) false
      (s, [.eitherDo p src env accept .nop es], [])
    else
      let follow := if afterMove != .nop && events.any (fun | .standardMoved .. => true | _ => false)
        then .cons afterMove es else es
      (next, [.run p src env follow], events)

/-- The Move or the payment question preserves the game invariants. -/
theorem moveEffectStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (a : Prim) (afterMove : Effect) (es : EffectList) (paid : Bool) :
    Safe s (moveEffectStep s p src env a afterMove es paid).1 := by
  unfold moveEffectStep
  split
  · exact Safe.refl s
  · rename_i next events h
    dsimp only
    split
    · exact Safe.refl s
    · exact applyPrim_safe h

/-- Each answer keeps the remaining groups containing that unit. Only units that distinguish
groups are offered, so an answer always reduces the number of alternatives (CR 355.11.b). -/
def retainTargetSetFrame (p : PlayerId) (src : ObjId) (env : Env)
    (groups : List (List ObjId)) (es : EffectList) : Frame :=
  let remaining := match env.lookup pickVar with
    | some (.obj id) => groups.filter (·.contains id)
    | _ => groups
  let candidates := remaining.flatten.eraseDups.filter
    (fun id => remaining.any (fun group => !group.contains id))
  match candidates with
  | id :: more => .pickDo p src env id more (.retainTargetSet remaining) es
  | [] =>
    let retained := remaining.headD []
    .run p src { env with
      slots := retained.map Value.obj
      targetObjs := env.targetObjs.filter retained.contains } es

/-- Ask the next player with more than one candidate, or record their sole pick and move on.
The original effect resumes after every player has picked (CR 355.10.e). -/
def collectOwnPicksFrame (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (remaining : List PlayerId) (place : Place) (fs : FilterList) (body : Effect)
    (capture : Bool) (es : EffectList) : Frame :=
  let env := if capture then
    { env with slots := env.slots ++ (env.lookup pickVar).toList }
    else env
  match remaining with
  | [] => .run p src env (.cons body es)
  | q :: qs =>
    let candidates := (s.pickCandidates q src env .friendly place fs false).getD []
    let next := .cons (.collectOwnPicks p qs place fs body false) es
    match candidates with
    | [] => .run p src env next
    | [id] => .run p src { env with slots := env.slots ++ [.obj id] } next
    | id :: other :: more =>
      .pickDo q src env id (other :: more) (.collectOwnPicks p qs place fs body true) es

/-- Offer the moving player only the Units that can reach the Battlefield. An impossible
instruction leaves the Board as it is (CR 391, 449). -/
def forceMoveToBattlefieldFrame (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (who : PlayerSel) (destination : Selector) (es : EffectList) : Frame :=
  let resume := Frame.run p src env es
  match who.resolve s p env, destination.eval s p src env with
  | some [actor], some [bf] =>
    if !(s.zone .battlefieldZone).contains bf || !(s.cardDef? bf).any (·.hasType .battlefield) then
      resume else
    let candidates := s.inPlay.filter (fun id => (s.cardDef? id).any (·.hasType .unit) &&
      !s.moveBlocked id &&
      !s.blocksEnemyMove (env.effectController.getD p) id &&
      (s.obj? id).any (fun o => o.controller == actor && s.effectMoveBattlefieldOk o bf))
    let slot := env.slots.length
    let bound := { env with slots := env.slots ++ [.obj bf] }
    let body := Effect.eachPlayer who (.prim (.move (.slot (slot + 1)) (.at_ (.slot slot))))
    match candidates with
    | [] => resume
    | [id] => .run p src { bound with slots := bound.slots ++ [.obj id] } (.cons body es)
    | id :: other :: more =>
      .pickDo actor src bound id (other :: more) (.collectOwnPicks p [] .anywhere .nil body true) es
  | _, _ => resume

/-- Use the destination chosen when the Spell was finalized (CR 355.4, 359.3.e).
A destination forbidden by the global movement rules requires a Recall (CR 449.2.c). -/
def chosenMove (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (slot : Nat) (allowBase : Bool) (fs : FilterList) (afterMove : Effect)
    (afterNegatedMove : Bool) : Env × Effect :=
  let unit := Selector.slot slot
  let resume := (env, Effect.nop)
  let negated := if afterNegatedMove then (env, afterMove) else resume
  let thenMove (move : Effect) : Effect :=
    if afterNegatedMove then .seqOf [move, afterMove] else .doThen move afterMove
  let effectPick := env.executionPick <|> (s.obj? src).map (·.spellPick)
  match effectPick.map SpellPick.effectChoice, env.slots[slot]? with
  | some (.destination dest), some (.obj id)
  | some (.modeDestination _ dest), some (.obj id) =>
    match s.obj? id, dest with
    | some o, none =>
      if !allowBase then resume
      else if o.loc.isNone || s.moveBlocked id || s.blocksEnemyMove (env.effectController.getD p) id then negated
      else (env, thenMove (.prim (.move unit .base)))
    | some o, some bf =>
      if !(s.zone .battlefieldZone).contains bf || !(s.cardDef? bf).any (·.hasType .battlefield) ||
          !(FilterList.holds s src env bf fs).getD false then resume
      else if o.loc == some bf || s.moveBlocked id ||
          s.blocksEnemyMove (env.effectController.getD p) id then negated
      else if !s.effectObjectMoveBattlefieldOk id o bf then
        let recallEffect : Effect := .prim (.recall unit false)
        (env, if afterNegatedMove then .seqOf [recallEffect, afterMove] else recallEffect)
      else (env.bind pickVar (.obj bf), thenMove (.prim (.move unit (.at_ (.var pickVar)))))
    | none, _ => resume
  | _, _ => resume

/-- Recycle the remaining looked-at cards. Put a random ordering decision before the rest
when at least two cards are Recycled together (CR 417.5). -/
def recycleLookedStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (es : EffectList) : GameState × List Frame × List Event :=
  let deck := s.zone (.player p .mainDeck)
  let remaining := deck.filter env.lookedCards.contains
  if 2 ≤ remaining.length then
    let keep := deck.filter (fun id => !env.lookedCards.contains id)
    (s, [.chancePredict p deck.length keep remaining, .run p src env es], [])
  else
    let r := recycleList remaining s
    (r.1, [.run p src env es], r.2 ++ (if remaining.isEmpty then [] else [.recycled p]))

/-- Recycling or asking for an order preserves the structural invariants. -/
theorem recycleLookedStep_safe (s : GameState) (p : PlayerId) (src : ObjId)
    (env : Env) (es : EffectList) : Safe s (recycleLookedStep s p src env es).1 := by
  unfold recycleLookedStep
  dsimp only
  split
  · exact Safe.refl s
  · exact recycleList_safe _ _

/-- A Recycle ordering decision and its continuation are both play frames. -/
theorem recycleLookedStep_mem {s : GameState} {p : PlayerId} {src : ObjId}
    {env : Env} {es : EffectList} {f : Frame} (h : f ∈ (recycleLookedStep s p src env es).2.1) :
    f.isPlay = true := by
  unfold recycleLookedStep at h
  dsimp only at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  · simp only [List.mem_singleton] at h
    subst f
    rfl

/-- Mandatory locations imposed by resolving a Hidden spell or the play effect of a Unit
that was played from hiding (CR 811.1.d.5). -/
def Env.hiddenPlayRequirements (env : Env) : List (List (Option ObjId)) :=
  env.hiddenPlayLocation.toList.map (fun b => [some b])

/-- Build an effect play's requirements from its own location instruction and the Hidden effect. -/
def Env.permanentPlayTerms (env : Env) (price : EffectPlayPrice) (places : Option (List ObjId))
    (baseOnly : Bool := false) : EffectPlayTerms :=
  let requiredBase := if baseOnly then [[none]] else []
  { price, requirements := requiredBase ++ env.hiddenPlayRequirements ++ places.toList.map (·.map some) }

/-- The otherwise matching candidates for an effect's optional play. These are play choices,
rather than targets. -/
def effectPlayCandidates (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (sel : Selector) : List ObjId :=
  match sel with
  | .pick .one side place fs => (s.pickCandidates p src env side place fs false).getD []
  | _ => (sel.eval s p src env).getD []

/-- The card has at least one legal, fundable finalization through the effect. -/
def effectCardPlayable (s : GameState) (p : PlayerId) (card : ObjId) (env : Env)
    (price : EffectPlayPrice) (funding : EffectAddPolicy) (baseOnly : Bool := false) : Bool :=
  (s.locate card).isSome &&
    if (s.cardDef? card).any (·.hasType .spell) then
      !baseOnly && !(limitedSpellChoices s p card price funding).isEmpty
    else !(fundablePermanentChoices s p card (env.permanentPlayTerms price none baseOnly) funding).isEmpty

/-- Offer each fundable finalization for a permanent. A mandatory Battlefield fee may be
    declined (CR 355.17). -/
def fundedPermanentOptions (s : GameState) (p : PlayerId) (card : ObjId) (terms : EffectPlayTerms)
    (funding : EffectAddPolicy) : Effect :=
  let plans := fundablePermanentChoices s p card terms funding
  let choices := plans.map (fun (plan, hasAdds) =>
    if hasAdds then Effect.fundPermanentFromEffect card terms plan []
    else Effect.finishFundedPermanent card terms plan [])
  let decline := if plans.all (fun (plan, _) => !plan.battlefieldFees.isEmpty) then [.nop] else []
  .eitherOf (EffectList.ofList (choices ++ decline))

/-- Offer each fundable finalization for this effect's Unit or Gear. -/
def effectPermanentFinalizations (s : GameState) (p : PlayerId) (card : ObjId) (env : Env)
    (price : EffectPlayPrice) (funding : EffectAddPolicy) (baseOnly : Bool := false) : Effect :=
  fundedPermanentOptions s p card (env.permanentPlayTerms price none baseOnly) funding

/-- Continue a required limited Play, choosing only if more than one card is eligible. -/
def requiredCardPlayFrame (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (sel : Selector) (price : EffectPlayPrice) (funding : EffectAddPolicy) (es : EffectList)
    (baseOnly : Bool) : Frame :=
  let cards := (effectPlayCandidates s p src env sel).filter (fun id =>
    (s.obj? id).any (·.kind.phys?.isSome) && effectCardPlayable s p id env price funding baseOnly)
  let play := Effect.playOfferedCard cards 1 price baseOnly
  match cards with
  | [] => .run p src env es
  | [card] => .run p src (env.bindPick card false) (.cons play es)
  | first :: more => .pickDo p src env first more play es

/-- Continuing a limited Play keeps the engine in play. -/
theorem requiredCardPlayFrame_play (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (sel : Selector) (price : EffectPlayPrice) (funding : EffectAddPolicy) (es : EffectList)
    (baseOnly : Bool) : (requiredCardPlayFrame s p src env sel price funding es baseOnly).isPlay = true := by
  unfold requiredCardPlayFrame
  dsimp only
  split <;> rfl

/-- When an effect offers to play a card to a required location, its resolution picks must have a
legal finalization (CR 355.16, 355.17). -/
def requiredPlayCandidates (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (e : Effect) (funding : EffectAddPolicy) : Option (List ObjId) :=
  match e with
  | .prim (.createAt name _ (.pick .one side place fs) _) => do
    let some token := s.tokenCard name | return []
    let candidates ← s.pickCandidates p src env side place fs false
    return candidates.filter (s.tokenFieldAllowed p src token)
  | .prim (.castInline sel) =>
    let candidates := match sel with
      | .pick .one side place fs => s.pickCandidates p src env side place fs false
      | _ => sel.eval s p src env
    some ((candidates.getD []).filter (fun card =>
      !(limitedSpellChoices s p card .ignoreEnergy funding).isEmpty))
  | .prim (.playReduced sel less none) => do
    let some amount := less.evalS s p src env | return []
    let candidates := match sel with
      | .pick .one side place fs => s.pickCandidates p src env side place fs false
      | _ => sel.eval s p src env
    return (candidates.getD []).filter (fun card =>
      !(s.cardDef? card).any (·.hasType .spell) ||
        !(limitedSpellChoices s p card (.reduceEnergy amount) funding).isEmpty)
  | .prim (.playReduced sel less (some dest)) => do
    let some amount := less.evalS s p src env | return []
    let candidates := match sel with
      | .pick .one side place fs => s.pickCandidates p src env side place fs false
      | _ => sel.eval s p src env
    let terms := env.permanentPlayTerms (.reduceEnergy amount)
      (some ((dest.eval s p src env).getD []))
    return (candidates.getD []).filter (fun card => !(permanentPlayPlans s p card terms).isEmpty)
  | _ => none

/-- A Legend registered for this player and left outside the game can enter while its
source is on the Board. The move preserves the physical card (CR 103.1). -/
def addReservedLegend (s : GameState) (p : PlayerId) (src legend : ObjId) :
    GameState × List Event :=
  let reserve := Zone.player p .reserveLegends
  let destination := Zone.player p .legendZone
  if s.inPlay.contains src && (s.zone reserve).contains legend &&
      (s.cardDef? legend).any (·.hasType .legend) then
    match moveObj s legend destination .bottom with
    | some (t, added) =>
      (t.modObj added (fun o => { o with reservedBy := some src }),
        [.moved legend added destination])
    | none => (s, [])
  else (s, [])

/-- Bringing a registered Legend into the game preserves the state's invariants. -/
theorem addReservedLegend_safe (s : GameState) (p : PlayerId) (src legend : ObjId) :
    Safe s (addReservedLegend s p src legend).1 := by
  unfold addReservedLegend
  dsimp only
  split
  · split
    · rename_i t id h
      exact (Safe.moveObj h).trans (Safe.modObj t id (fun _ => rfl) (fun _ => rfl))
    · exact Safe.refl s
  · exact Safe.refl s

/-- The activation can choose an available registered Legend only while the Unit is on the Board. -/
def addReservedLegendFrame (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (rest : EffectList) : Frame :=
  if s.inPlay.contains src then
    let candidates := (s.zone (.player p .reserveLegends)).filter (fun card =>
      (s.cardDef? card).any (·.hasType .legend))
    match candidates with
    | [] => .run p src env rest
    | [legend] => .run p src env (.cons (.addReservedLegendChosen legend) rest)
    | first :: more => .pickDo p src env first more .addReservedLegendPicked rest
  else .run p src env rest

theorem addReservedLegendFrame_play (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (rest : EffectList) : (addReservedLegendFrame s p src env rest).isPlay = true := by
  unfold addReservedLegendFrame
  split
  · dsimp only
    split <;> rfl
  · rfl

/-- Use the shared finalization choices for optional costs, battlefield fees, and mandatory
locations (CR 355.1.a, 355.17). -/
def permanentPlayEffects (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (pr : Prim) : Option (Env × EffectList) :=
  let needsChoices (id : ObjId) := (s.cardDef? id).any (fun d =>
    ((d.discardToPlay || d.playExtra.isSome || d.showOffRequirement.isSome ||
      !(s.extrasRaw p id d).isEmpty) &&
      (d.hasType .unit || d.hasType .gear)) ||
      (d.hasType .unit && (env.hiddenPlayLocation.isSome ||
        !(s.battlefieldFeeChoices p id d).isEmpty)))
  let schedule (ids : List ObjId) (price : EffectPlayPrice)
      (places : Option (List ObjId)) (mandatory : Bool := false) :=
    if mandatory || ids.any needsChoices then
      let terms := env.permanentPlayTerms price places
      some (env, EffectList.ofList (ids.map (fun card => .planPermanentPlay card terms)))
    else none
  let locations (sel : Selector) := (sel.eval s p src env).getD []
  match pr with
  | .play sel => schedule (locations sel) .ignoreBase none
  | .playAtBase sel =>
    let terms : EffectPlayTerms := {
      price := .ignoreBase
      requirements := [none] :: env.hiddenPlayRequirements }
    some (env, EffectList.ofList ((locations sel).map (fun card => .planPermanentPlay card terms)))
  | .playPaying sel => schedule (locations sel) .ignoreEnergy none
  | .playTo sel dest =>
    if sel == .self && s.playingFromHidden p src && (s.fxOf p).contains .nextUnitAnywhereBuffed &&
        (s.cardDef? src).any (·.hasType .unit) then
      let terms : EffectPlayTerms := {
        price := .ignoreBase, requirements := [(s.playBfOptions p src).map some] }
      some (env, .cons (.planPermanentPlay src terms) .nil)
    else schedule (locations sel) .ignoreBase (some (locations dest))
  | .playReduced sel less dest => do
    let amount ← less.evalS s p src env
    schedule (locations sel) (.reduceEnergy amount) (dest.map locations) dest.isSome
  | .playBanishedWith =>
    let ids := (s.zone (.player p .banishment)).filter (fun id =>
      (s.obj? id).any (·.banishedWith == some src) && (s.cardDef? id).any (·.hasType .unit))
    schedule ids .ignoreBase none
  | .playFirst fs => do
    let deck := s.zone (.player p .mainDeck)
    let card ← deck.find? (fun id => fs.holds s src env id == some true)
    let (ctx, play) ← schedule [card] .ignoreBase none
    let previous := deck.takeWhile (· != card)
    some ({ ctx with slots := previous.map Value.obj },
      play.append (.cons (.prim (.recycle (.slotsFrom 0))) .nil))
  | _ => none

/-- After Banish, finalize the new play with the player and location the effect specifies.
The original controller resolves the rest of the effect (CR 355.17, 420.3, 428). -/
def replayFrames (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (id : ObjId)
    (replay : BanishReplay) (events : List Event) (es : EffectList) : List Frame :=
  match s.obj? id, banishedPlayId events with
  | some original, some card =>
    let (player, locations) := match replay with
      | .byOwner => (original.owner, [])
      | .sameLocation =>
        (original.owner, [if s.foreignBase id original.owner then [] else [original.loc]])
      | .toBase => (p, [[none]])
    let hidden := if player == p then env.hiddenPlayRequirements else []
    let terms : EffectPlayTerms := { price := .ignoreBase, requirements := locations ++ hidden }
    [.run player src env (.cons (.planPermanentPlay card terms) .nil), .run p src env es]
  | _, _ => [.run p src env es]

/-- The continuation of replay contains only frames of play. -/
theorem replayFrames_mem {s : GameState} {p : PlayerId} {src id : ObjId} {env : Env}
    {replay : BanishReplay} {events : List Event} {es : EffectList} {f : Frame}
    (h : f ∈ replayFrames s p src env id replay events es) : f.isPlay = true := by
  unfold replayFrames at h
  split at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  · rcases h with rfl | rfl <;> rfl
  · subst f
    rfl

/-- Banish the whole group before its owners order their plays. Tokens disappear without
    a replay (CR 185.6, 428). -/
def banishReplayGroup (p : PlayerId) : List ObjId → GameState →
    GameState × List (PlayerId × ObjId × Option ObjId) × List Event
  | [], s => (s, [], [])
  | id :: more, s =>
    let banished := banishObj p s id
    let t := banishReplayGroup p more banished.1
    let replays := match s.obj? id, banishedPlayId banished.2 with
      | some original, some card => (original.owner, card, original.loc) :: t.2.1
      | _, _ => t.2.1
    (t.1, replays, banished.2 ++ t.2.2)

/-- Banishing the group preserves the game's structural invariants. -/
theorem banishReplayGroup_safe (p : PlayerId) :
    ∀ ids s, Safe s (banishReplayGroup p ids s).1
  | [], s => Safe.refl s
  | id :: more, s => (banishObj_safe p s id).trans (banishReplayGroup_safe p more _)

/-- Put the ordered replays onto the Chain before any of them finalizes (CR 303.2.a, 354.2). -/
def queueBanishReplays (p : PlayerId) (src : ObjId) (env : Env) :
    List (PlayerId × ObjId × Option ObjId) → GameState → GameState × List Frame × List Event
  | [], s => (s, [], [])
  | (owner, card, field) :: rest, s =>
    match moveObj s card .chain with
    | some (t, pending) =>
      let later := queueBanishReplays p src env rest t
      let ctx := if owner == p then env else { env with hiddenPlayLocation := none }
      let finalize := EffectList.ofList [.planBanishReplay pending field, .cancelBanishReplay pending]
      (later.1, .run owner src ctx finalize :: later.2.1, .moved card pending .chain :: later.2.2)
    | none => queueBanishReplays p src env rest s

theorem queueBanishReplays_safe (p : PlayerId) (src : ObjId) (env : Env)
    (cards : List (PlayerId × ObjId × Option ObjId)) (s : GameState) :
    Safe s (queueBanishReplays p src env cards s).1 := by
  induction cards generalizing s with
  | nil => exact Safe.refl s
  | cons replay rest ih =>
    obtain ⟨owner, card, field⟩ := replay
    unfold queueBanishReplays
    split
    · rename_i t pending moved
      exact (Safe.moveObj moved).trans (ih t)
    · exact ih s

theorem queueBanishReplays_mem (p : PlayerId) (src : ObjId) (env : Env)
    (cards : List (PlayerId × ObjId × Option ObjId)) (s : GameState) {f : Frame} :
    f ∈ (queueBanishReplays p src env cards s).2.1 → f.isPlay = true := by
  induction cards generalizing s with
  | nil => simp [queueBanishReplays]
  | cons replay rest ih =>
    obtain ⟨owner, card, field⟩ := replay
    unfold queueBanishReplays
    split
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact ih _ h
    · exact ih s

/-- Return a replay that could not finalize to its previous zone. A successful play has
already removed the pending object from the Chain (CR 358.5). -/
def cancelBanishReplay (s : GameState) (p : PlayerId) (card : ObjId) : GameState × List Event :=
  if (s.zone .chain).contains card then
    match moveObj s card (.player p .banishment) with
    | some (t, returned) => (t, [.moved card returned (.player p .banishment)])
    | none => (s, [])
  else (s, [])

theorem cancelBanishReplay_safe (s : GameState) (p : PlayerId) (card : ObjId) :
    Safe s (cancelBanishReplay s p card).1 := by
  unfold cancelBanishReplay
  split
  · split
    · rename_i t returned moved
      exact Safe.moveObj moved
    · exact Safe.refl s
  · exact Safe.refl s

/-- Owners order their cards before the first permanent finalizes (CR 303.2.a, 334, 354.3). -/
def orderBanishReplayFrames (p : PlayerId) (src : ObjId) (env : Env)
    (remaining ordered : List (PlayerId × ObjId × Option ObjId)) (es : EffectList)
    (s : GameState) : GameState × List Frame × List Event :=
  match remaining with
  | [] =>
    let queued := queueBanishReplays p src env ordered.reverse s
    (queued.1, queued.2.1 ++ [.run p src env es], queued.2.2)
  | (owner, first, location) :: rest =>
    let others := (rest.takeWhile (fun entry => entry.1 == owner)).map (·.2.1)
    if others.isEmpty then
      let next := Effect.orderBanishReplays rest ((owner, first, location) :: ordered)
      (s, [.run p src env (.cons next es)], [])
    else (s, [.pickDo owner src env first others (.recordBanishReplay p remaining ordered) es], [])

theorem orderBanishReplayFrames_safe (p : PlayerId) (src : ObjId) (env : Env)
    (remaining ordered : List (PlayerId × ObjId × Option ObjId)) (es : EffectList) (s : GameState) :
    Safe s (orderBanishReplayFrames p src env remaining ordered es s).1 := by
  unfold orderBanishReplayFrames
  split
  · exact queueBanishReplays_safe _ _ _ _ _
  · dsimp only
    split <;> exact Safe.refl s

/-- Ordering and finalizing the replays use play frames only. -/
theorem orderBanishReplayFrames_mem {p : PlayerId} {src : ObjId} {env : Env}
    {remaining ordered : List (PlayerId × ObjId × Option ObjId)} {es : EffectList}
    {s : GameState} {f : Frame}
    (h : f ∈ (orderBanishReplayFrames p src env remaining ordered es s).2.1) : f.isPlay = true := by
  unfold orderBanishReplayFrames at h
  split at h
  · rcases List.mem_append.mp h with h | h
    · exact queueBanishReplays_mem _ _ _ _ _ h
    · obtain rfl := List.mem_singleton.mp h
      rfl
  · dsimp only at h
    split at h <;> obtain rfl := List.mem_singleton.mp h <;> rfl

/-- "As this is attached" instructions run after the attachment event has been observed
(CR 370.1.b.1, 725.1). Each receives the newly equipped Unit in slot 0. -/
def attachmentReplacementFrames (s : GameState) (events : List Event) : List Frame :=
  events.flatMap (fun
    | .attached gear unit =>
      match s.obj? gear, s.cardDef? gear with
      | some o, some d =>
        let env : Env := { slots := [.obj unit] }
        let effects := d.fullAbilities.filterMap (fun
          | .replacement .attach cond body =>
            if cond.eval s o.controller gear env == some true then some body.body else none
          | _ => none)
        effects.map (fun body => .run o.controller gear env (.cons body .nil))
      | _, _ => []
    | _ => [])

/-- An attachment replacement only adds effect-resolution work. -/
theorem attachmentReplacementFrames_play {s : GameState} {events : List Event} {f : Frame}
    (h : f ∈ attachmentReplacementFrames s events) : f.isPlay = true := by
  obtain ⟨ev, _, h⟩ := List.mem_flatMap.mp h
  cases ev <;> simp only [List.not_mem_nil] at h
  split at h
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
    rfl
  · contradiction

/-- Offer complete new finalization choices, or let the Spell keep the original ones. -/
def remakeSpellChoicesFrame (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (spell : Selector) (es : EffectList) : Frame :=
  let options := ((spell.eval s p src env).getD []).flatMap (fun id =>
    match s.obj? id, s.cardDef? id with
    | some item, some d =>
      if !d.hasType .spell then [] else
        d.spellEffect.toList.flatMap (fun effect =>
          if !effect.hasFinalizationChoice then [] else
            let choices := spellChoicesWithShowOff s p id d effect [item.spellPick.showOffObject]
              item.spellPick.variablePower (some item.spellPick.paysXP)
            let executions := if d.usesRepeatChoices then repeatSpellChoices choices item.extraPaid
              else choices
            executions.map (fun (pick, targets) => .setSpellChoices id pick targets))
    | _, _ => [])
  if options.isEmpty then .run p src env es
  else .mayDo p src env (.eitherOf (EffectList.ofList options)) es

/-- The slots of a Spell or an ability: the objects chosen, and a filler for each target of up to one that was
left out (it selects nothing). -/
def slotValues (ts : List ObjId) (e : Option EffectDef) : List Value :=
  let n := (e.map (fun d => (d.choices.filter Choice.isTarget).length)).getD 0
  ts.map Value.obj ++ List.replicate (n - ts.length) (Value.int 0)

/-- Recheck independent target slots or a single bounded group (CR 359.3.e.2).
Invalid targets leave an empty value in their original slot. -/
def recheckedSlots (s : GameState) (p : PlayerId) (src : ObjId) (ts : List ObjId)
    (definition : Option EffectDef) : List Value :=
  match definition with
  | some e =>
    let choices := e.choices.filter Choice.isTarget
    let might := s.mightTable
    let check (choice : Choice) (i : Nat) : Value :=
      match ts[i]? with
      | some id =>
        if (choice.candidatesAfter s p src might (ts.take i)).contains id then .obj id
        else .int 0
      | none => .int 0
    match choices.getLast? with
    | some (choice@(.target (.upTo n) ..)) | some (choice@(.target (.exactly n) ..)) =>
      let fixed := choices.dropLast
      let group := ts.drop fixed.length
      let valid := choice.candidatesAfter s p src might (ts.take fixed.length)
      fixed.zipIdx.map (fun (c, i) => check c i) ++
        (group.take n).map (fun id => if valid.contains id then .obj id else .int 0) ++
        List.replicate (n - group.length) (.int 0)
    | _ => choices.zipIdx.map (fun (c, i) => check c i)
  | none => []

/-- Recheck recorded choices, including targets newly protected from enemy effects (CR 758.1). -/
def finalizedSlots (s : GameState) (p : PlayerId) (src : ObjId) (ts : List ObjId)
    (definition : Option EffectDef) (pick : SpellPick) : List Value :=
  let changedController := s.playLog.any (fun play =>
    play.object == src && play.moment == .finalized && play.who != p)
  if pick != .plain || definition.any (·.recheckTargets) || changedController ||
      (s.obj? src).any (·.hiddenAt.isSome) || ts.any (s.blocksChoice p) then
    recheckedSlots s p src ts definition
  else slotValues ts definition

/-- Before a group resolves, keep only legal original targets. When a shared restriction no
longer holds, retain a maximal legal subset (CR 355.11.b, 359.3.e.2). -/
def EffectDef.recheckTargetGroup (e : EffectDef) (s : GameState) (p : PlayerId)
    (src : ObjId) (targets : List ObjId) (body : EffectList) : EffectList :=
  match e.choices.getLast? with
  | some c =>
    match c with
    | .target (.atOneBattlefield n) _ _ _ =>
      let fixed := targets.take (e.choices.length - 1)
      let legal := c.candidatesAfter s p src s.mightTable fixed
      let original := (targets.drop fixed.length).filter legal.contains
      let groups := (s.targetsByBattlefield original).flatMap (fun group =>
        match group with
        | [] => []
        | first :: _ =>
          let total := n + s.bonusOn p src first
          if group.length ≤ total then [group] else
            (subseqsUpTo total group).filter (fun subset => subset.length == total))
      let remaining := if groups.isEmpty then [fixed] else groups.map (fixed ++ ·)
      .cons (.retainTargetSet remaining) body
    | .target .anyNumber _ _ _ | .target (.combinedMightAtMost _) _ _ _ |
        .target (.exactly _) _ _ _ =>
      let fixed := targets.take (e.choices.length - 1)
      let pm := s.mightTable
      let legal := c.candidatesAfter s p src pm fixed
      let original := (targets.drop fixed.length).filter legal.contains
      let weight := c.groupWeight s pm
      let limit := c.groupLimit
      let total (ids : List ObjId) := (ids.map weight).sum
      let groups := if total original ≤ limit then [original] else
        (subseqsWithin weight limit original).filter (fun group =>
          original.all (fun id => group.contains id || decide (limit < total group + weight id)))
      .cons (.retainTargetSet (groups.map (fixed ++ ·))) body
    | _ => body
  | none => body

/-- Recheck this execution's locked targets against the current state (CR 359.3.e.2, 820.2).
A previous execution may already have changed those targets. -/
def spellExecutionFrames (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (pick : SpellPick) (targets : List ObjId) : List Frame := Id.run do
  let definition := (s.cardDef? src).bind (·.spellForPick pick)
  let some body := definition | return []
  let ctx := { env with
    slots := recheckedSlots s p src targets definition
    targetObjs := targets
    executionPick := some pick
    playerTargets := if s.spellPlayerTargetOk p body pick then pick.playerTarget.toList else [] }
  let effects := body.recheckTargetGroup s p src targets (.cons body.body .nil)
  return [.run p src ctx effects]

/-- Every way to give each target at least one damage while assigning the entire amount. -/
def damageDivisions : List ObjId → Nat → List (List (ObjId × Nat))
  | [], total => if total == 0 then [[]] else []
  | [target], total => if total == 0 then [] else [[(target, total)]]
  | target :: next :: more, total =>
    (List.range (total - (next :: more).length)).flatMap (fun i =>
      (damageDivisions (next :: more) (total - (i + 1))).map ((target, i + 1) :: ·))

/-- Every offered division accounts for the whole amount and gives each target positive damage. -/
theorem damageDivisions_valid :
    ∀ {targets : List ObjId} {total : Nat} {hits : List (ObjId × Nat)},
      hits ∈ damageDivisions targets total →
        hits.map Prod.fst = targets ∧ (hits.map Prod.snd).sum = total ∧
          ∀ hit ∈ hits, 0 < hit.2
  | [], total, hits, h => by
    by_cases hz : total = 0
    · subst total
      simp only [damageDivisions, beq_self_eq_true, ite_true, List.mem_singleton] at h
      subst hits
      simp
    · simp [damageDivisions, hz] at h
  | [target], total, hits, h => by
    by_cases hz : total = 0
    · simp [damageDivisions, hz] at h
    · simp only [damageDivisions, beq_iff_eq, hz, ite_false, List.mem_singleton] at h
      subst hits
      simp [Nat.pos_of_ne_zero hz]
  | target :: next :: more, total, hits, h => by
    obtain ⟨i, hi, hh⟩ := List.mem_flatMap.mp h
    obtain ⟨suffix, hs, rfl⟩ := List.mem_map.mp hh
    obtain ⟨ht, hd, hp⟩ := damageDivisions_valid hs
    have hbound := List.mem_range.mp hi
    refine ⟨by simp [ht], ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, hd]
      omega
    · intro hit hm
      rcases List.mem_cons.mp hm with rfl | hn
      · simp
      · exact hp _ hn

/-- Choose between the Equipment's printed ways of paying before attaching (CR 821). -/
def equipWithCostFrame (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (gear recipient : Selector) (less : Nat) (es : EffectList) : Frame :=
  let resourcePayment := Effect.prim (.attachPaying gear recipient less)
  let useResources := Frame.run p src env (.cons resourcePayment es)
  match gear.eval s p src env, recipient.eval s p src env with
  | some [g], some [u] =>
    if (s.cardDef? g).any CardDef.equipCanExhaust then
      if !s.inPlay.contains g || !s.inPlay.contains u ||
          !(s.cardDef? u).any (·.hasType .unit) || (s.cardDef? g).any (·.hasType .unit) ||
          s.controllerOf g != p || s.controllerOf u != p || (s.obj? g).any (·.attached == some u) then
        .run p src env es
      else
        let filters := FilterList.ofList [.ofType .unit, .ready]
        let payer := Selector.pick .one .friendly .anywhere filters
        if (s.pickCandidates p src env .friendly .anywhere filters false).any (fun candidates => !candidates.isEmpty) then
          let exhaust := Effect.doThen (.prim (.exhaust payer)) (.prim (.attach gear recipient))
          .eitherDo p src env resourcePayment exhaust es
        else useResources
    else useResources
  | _, _ => useResources

/-- An Equip payment choice stays inside the resolution of the current item. -/
theorem equipWithCostFrame_play (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (g u : Selector) (less : Nat) (es : EffectList) :
    (equipWithCostFrame s p src env g u less es).isPlay = true := by
  unfold equipWithCostFrame
  split
  · dsimp only
    split
    · split
      · rfl
      · split <;> rfl
    · rfl
  · rfl

/-- Count only the chosen objects killed by this instruction, including a token that ceased to
exist. A replacement that saved a target and killed something else does not count. -/
def killedTargets (targets : List ObjId) (events : List Event) : Nat :=
  targets.countP (fun target => (killedController target events).isSome)

/-- Remember a delayed ability independently of what happens to its source afterward (CR 391). -/
def recordKillCount (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (index : Nat) (targets : List ObjId) (events : List Event) : GameState :=
  let amount := killedTargets targets events
  if amount == 0 then s else
    match env.sourceCard <|> (s.cardDef? src).map (·.id) with
    | some card => s.addTurnFxOn p src (.endTriggerWithAmount card index amount)
    | none => s

/-- Recording the received count changes only the turn notes. -/
theorem recordKillCount_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (index : Nat) (targets : List ObjId) (events : List Event) :
    Safe s (recordKillCount s p src env index targets events) := by
  unfold recordKillCount
  dsimp only
  split
  · exact Safe.refl s
  · split
    · exact addTurnFxOn_safe s _ _ _
    · exact Safe.refl s

/-- How the linked Kill instruction determines whether and for whom its continuation runs. -/
inductive KillFollowupKind where
  /-- Instruct the affected permanent's controller, even if a replacement saved it. -/
  | forController
  /-- Keep the resolving player and require a death caused by this Kill. -/
  | ifKilled

/-- The continuation and target preserved while a Kill waits for replacement choices. -/
structure KillFollowup where
  /-- The affected permanent's target slot. -/
  slot : Nat
  /-- The linked instruction. -/
  body : Effect
  /-- Which result of the Kill permits the continuation. -/
  kind : KillFollowupKind

/-- Reissue the same instruction after the player chooses its replacement. -/
def KillFollowup.retry (link : KillFollowup) : Effect :=
  match link.kind with
  | .forController => .killThenForController link.slot link.body
  | .ifKilled => .killThenIfKilled link.slot link.body

/-- A conditional continuation requires the target's death. A controller continuation can also
refer to the target if a replacement left it on the Board. -/
def linkedKillFrames (before s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (events : List Event) (linked : Option KillFollowup) : List Frame := Id.run do
  let some link := linked | return []
  let some (.obj id) := env.slots[link.slot]? | return []
  let player := match link.kind with
    | .forController =>
      if s.inPlay.contains id then (s.obj? id).map (·.controller)
      else directKilledController before id events
    | .ifKilled => (directKilledController before id events).map (fun _ => p)
  let some who := player | return []
  return [.run who src { env with effectController := env.effectController <|> some p }
    (.cons link.body .nil)]

/-- A linked instruction continues the current resolution. -/
theorem linkedKillFrames_play {before s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {events : List Event} {linked : Option KillFollowup} {f : Frame}
    (h : f ∈ linkedKillFrames before s p src env events linked) : f.isPlay = true := by
  unfold linkedKillFrames at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · obtain rfl := List.mem_singleton.mp h
        rfl
      · simp at h
    · simp at h
  · simp at h

/-- Kill the chosen objects, with any delayed ability or linked instruction (CR 359.3.e.14). -/
def killEffectStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (targets : Selector)
    (delay : Option Nat) (es : EffectList) (linked : Option KillFollowup := none) :
    GameState × List Frame × List Event :=
  let ids := (targets.eval s p src env).getD []
  match s.deathGroupChoice ids with
  | some (unit, controller, first, other) =>
    let retry := match linked with
      | some link => link.retry
      | none => delay.elim (.prim (.kill targets)) (.killThenAtEnd targets)
    (s, [.eitherDo controller unit {} first other .nil, .run p src env (.cons retry es)], [])
  | none =>
    match applyPrim s p src env (.kill targets) with
    | some (killed, events) =>
      let next := delay.elim killed (fun i => recordKillCount killed p src env i ids events)
      (next, attachmentReplacementFrames killed events ++ linkedKillFrames s next p src env events linked ++
        [.run p src env es], events)
    | none => (s, [.run p src env es], [.skipped src])

/-- Resolving a kill instruction and recording delayed abilities preserves invariants. -/
theorem killEffectStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (targets : Selector) (delay : Option Nat) (es : EffectList) {linked : Option KillFollowup} :
    Safe s (killEffectStep s p src env targets delay es linked).1 := by
  unfold killEffectStep
  dsimp only
  split
  · exact Safe.refl s
  · split
    · rename_i killed events hm
      refine (applyPrim_safe hm).trans ?_
      cases delay with
      | none => exact Safe.refl killed
      | some i => exact recordKillCount_safe killed p src env i _ events
    · exact Safe.refl s

/-- The frames of a kill instruction stay on the Chain's resolution stack. -/
theorem killEffectStep_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {targets : Selector} {delay : Option Nat} {es : EffectList} {linked : Option KillFollowup} {f : Frame}
    (h : f ∈ (killEffectStep s p src env targets delay es linked).2.1) : f.isPlay = true := by
  unfold killEffectStep at h
  dsimp only at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  · split at h
    · rcases List.mem_append.mp h with used | hr
      · rcases List.mem_append.mp used with hs | hl
        · exact attachmentReplacementFrames_play hs
        · exact linkedKillFrames_play hl
      · obtain rfl := List.mem_singleton.mp hr
        rfl
    · obtain rfl := List.mem_singleton.mp h
      rfl

/-- Interpret the original token play's placement before offering replacements (CR 184.2, 376). -/
def unitTokenBatchOf (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (pr : Prim) :
    Option UnitTokenBatch := do
  let (card, count, ready, destination, contest) ← match pr with
    | .create name n place ready => do
      let card ← s.tokenCard name
      let count ← n.evalS s p src env
      let dest ← match place with
        | .atBase => some none
        | .here => (s.hereOf src).map some <|> if s.baseHere src then some none else none
        | _ => none
      some (card, count, ready, dest, false)
    | .createAt name n dest ready => do
      let card ← s.tokenCard name
      let count ← n.evalS s p src env
      let field ← (dest.eval s p src env).bind List.head?
      if s.tokenFieldAllowed p src card field then some (card, count, ready, some field, true)
      else none
    | .createAtPrev name n ready => do
      let card ← s.tokenCard name
      let count ← n.evalS s p src env
      some (card, count, ready, (s.obj? src).bind (·.prevLoc), false)
    | .playUnitTokenAt name dest => do
      let card ← s.tokenCard name
      if (s.unitTokenDestinations p card).contains dest then some (card, 1, false, dest, true)
      else none
    | .cloneToken sel => do
      let [id] ← sel.eval s p src env | none
      let o ← s.obj? id
      let .token card := o.kind | none
      let d ← s.cards.find? ((s.attachmentCopyOf id o).elim card (·.card))
      if o.controller == p then some (d, 1, !o.exhausted, o.loc, false) else none
    | _ => none
  if card.hasType .unit && count > 0 then
    some { destination, contest, entries := List.replicate count (card.id, ready) }
  else none

/-- Prepare entry with the card and original target that the reflexive ability will use. -/
def linkedUnitTokenBatch (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (name : String) (count : Nat) (place : Place) (ready : Bool) (index : Nat)
    (target : Option Selector) : Option UnitTokenBatch := do
  let card ← env.sourceCard <|> (s.cardDef? src).map (·.id)
  let batch ← if place == .here && (s.cards.find? card).any (·.hasType .legend) then do
    let [field] ← env.eventBattlefields.getD [] | none
    let token ← (s.tokenCard name).filter (fun d => CardDef.hasType d .unit)
    if !s.battlefields.contains field || count == 0 then none
    else some {
      destination := some field
      contest := false
      entries := List.replicate count (token.id, ready) }
  else unitTokenBatchOf s p src env (.create name (.const count) place ready)
  let targetId ← match target with
    | none => some none
    | some sel => do
      let [id] ← sel.eval s p src env | none
      some (some id)
  some { batch with followup := some ⟨src, card, index, targetId⟩ }

/-- The Unit token replacements currently offered by this player's effects (CR 370-371). -/
def GameState.unitTokenReplacements (s : GameState) (p : PlayerId) : List UnitTokenReplacement :=
  let sources := s.passiveSources.flatMap fun id =>
    if (s.obj? id).any (·.controller == p) then (s.activeMods id).map (id, ·) else []
  let substitutes := (sources.filterMap fun (_, mod) =>
    match mod with
    | .replaceUnitTokenWith name => ((s.tokenCard name).filter (·.hasType .unit)).map (·.id)
    | _ => none).eraseDups
  let duplicates := (sources.filterMap fun (src, mod) =>
    match mod with
    | .duplicateUnitTokenOnce =>
      let copy := s.copyStamp? src
      if s.turnFx.any (·.appliesTo s.turn src (.duplicatedUnitToken copy)) then none
      else some (UnitTokenReplacement.duplicate src copy)
    | _ => none).eraseDups
  (if substitutes.isEmpty then [] else [.substitute substitutes]) ++ duplicates

/-- Charge each elected replacement to the source that supplied it (CR 371). -/
def noteUnitTokenDuplicates (p : PlayerId) (s : GameState)
    (sources : List (ObjId × Option Timestamp)) : GameState :=
  sources.foldl (fun t (id, copy) => t.addTurnFxOn p id (.duplicatedUnitToken copy)) s

/-- Recording uses leaves the structural invariants intact. -/
theorem noteUnitTokenDuplicates_safe (p : PlayerId) (s : GameState)
    (sources : List (ObjId × Option Timestamp)) : Safe s (noteUnitTokenDuplicates p s sources) := by
  induction sources generalizing s with
  | nil => exact Safe.refl s
  | cons x rest ih => exact (addTurnFxOn_safe s p x.1 (.duplicatedUnitToken x.2)).trans (ih _)

/-- Add a chosen entry without publishing token plays until the whole group is on the Board. -/
def enterUnitToken (s : GameState) (p : PlayerId) (dest : Option ObjId) (after : GameState)
    (entry : CardId × Bool) : GameState :=
  let ready := entry.2 || (s.cards.find? entry.1).any (fun d => s.tokenReady p d dest)
  createOne entry.1 p dest ready after

/-- Placing each token preserves the structural invariants. -/
theorem enterUnitToken_safe (s : GameState) (p : PlayerId) (dest : Option ObjId) :
    ∀ (entries : List (CardId × Bool)) (t : GameState),
      Safe t (entries.foldl (enterUnitToken s p dest) t)
  | [], t => Safe.refl t
  | _entry :: more, t =>
    (createOne_safe _ _ _ _ t).trans (enterUnitToken_safe s p dest more _)

/-- Put the chosen group on the Board at once (CR 184.2, 375-376). -/
def enterUnitTokenBatch (s : GameState) (p : PlayerId) (batch : UnitTokenBatch) :
    GameState × List Event :=
  let marked := noteUnitTokenDuplicates p s batch.duplicatedBy
  let t := batch.entries.foldl (enterUnitToken s p batch.destination) marked
  let next := if batch.contest then batch.destination.elim t (fun field => contestFor p field t)
    else t
  let played := tokenPlays s next p
  let linked := batch.followup.toList.flatMap fun link =>
    let tokens := played.filterMap (fun | .tokenPlayed _ id => some id | _ => none)
    if tokens.isEmpty then []
    else [.unitTokensFor p link.source link.card link.index link.target tokens batch.destination]
  (buffNewTokens s next p, played ++ linked)

/-- Placing the whole group preserves the structural invariants. -/
theorem enterUnitTokenBatch_safe (s : GameState) (p : PlayerId) (batch : UnitTokenBatch) :
    Safe s (enterUnitTokenBatch s p batch).1 := by
  unfold enterUnitTokenBatch
  dsimp only
  exact (noteUnitTokenDuplicates_safe p s batch.duplicatedBy).trans
    ((enterUnitToken_safe s p batch.destination batch.entries _).trans (by
      split
      · cases batch.destination
        · exact buffNewTokens_safe _ _ _
        · exact (contestFor_safe _ _ _).trans (buffNewTokens_safe _ _ _)
      · exact buffNewTokens_safe _ _ _))

/-- Accelerate on a neutral Unit token, after flexible additional-cost reductions and any
discount on the next Unit play (CR 185.3, 356.4, 805). -/
def unitTokenAccelerateCosts (s : GameState) (p : PlayerId) : List Cost :=
  let less := s.nextUnitDiscount p
  let cost := (⟨1, [.any]⟩ : Cost).cutOptions (s.extraCuts p).1
  (cost.map (fun c => (c.lessEnergy less.1).lessPower less.2)).eraseDups

/-- Pay from eligible resources. A Power reserved for Gear cannot pay for a Unit token. -/
def payUnitTokenAccelerate (s : GameState) (p : PlayerId) (pay : RunePool.Payment) :
    Option (GameState × List Event) := do
  if !(s.fxOf p).contains .nextUnitAccelerate ||
      !(unitTokenAccelerateCosts s p).any (fun c => c.paidBy [] pay) then none else
    let runes ← s.runeCover p pay true (s.restrictedFor p false true)
    let (t, events) ← applyRunes s p runes
    let pool ← t.spendFor p false pay true true
    let paid := t.setPool p pool
    let spent := (t.poolOf p).any - pool.any
    some ({ paid with turnFx := t.spendPowerNotes p false true spent paid.turnFx }, events)

/-- Paying for a token preserves the structural invariants. -/
theorem payUnitTokenAccelerate_safe {s : GameState} {p : PlayerId} {pay : RunePool.Payment}
    {r : GameState × List Event} (h : payUnitTokenAccelerate s p pay = some r) : Safe s r.1 := by
  unfold payUnitTokenAccelerate at h
  split at h
  · contradiction
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, _, ⟨t, events⟩, ht, pool, _, rfl⟩ := h
    exact (applyRunes_safe _ ht).trans ((setPool_safe t p pool).trans
      ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
        fun _ hown => hown.congr rfl rfl, rfl⟩)

/-- Offer optional Accelerate payments that the player can fund. -/
def GameState.priceUnitToken (s : GameState) (p : PlayerId) (batch : UnitTokenBatch)
    (funding : EffectAddPolicy) : Effect :=
  let ordinary := Effect.finishUnitTokens batch none []
  if !(s.fxOf p).contains .nextUnitAccelerate || batch.entries.isEmpty then ordinary else
    let payments := ((unitTokenAccelerateCosts s p).flatMap (·.payments [])).eraseDups
    let options := payments.filterMap (fun pay =>
      let adds := funding.choices s p (fun t => (payUnitTokenAccelerate t p pay).isSome)
      if !adds.isEmpty then some (Effect.fundTokenAccelerate batch (pay.energy, pay.power) [])
      else if (payUnitTokenAccelerate s p pay).isSome then
        some (Effect.finishUnitTokens batch (some (pay.energy, pay.power)) [])
      else none)
    .eitherOf (EffectList.ofList (ordinary :: options))

/-- Extend the payment plan with eligible Add abilities before committing the token play. -/
def fundUnitTokenOptions (s : GameState) (p : PlayerId) (batch : UnitTokenBatch)
    (payment : RunePool.Payment) (adds : List EffectAdd) (funding : EffectAddPolicy) : List Effect :=
  match funding.applyAll s p adds with
  | none => [.finishUnitTokens batch none []]
  | some (t, _) =>
    let choices := funding.choices t p (fun u => (payUnitTokenAccelerate u p payment).isSome)
    let confirm := if (payUnitTokenAccelerate t p payment).isSome then
      [Effect.finishUnitTokens batch (some (payment.energy, payment.power)) adds] else []
    confirm ++ choices.map (fun a => .fundTokenAccelerate batch (payment.energy, payment.power) (adds ++ [a])) ++
      [.finishUnitTokens batch none []]

/-- Commit payment and entry together, with only the first token receiving Accelerate. -/
def finishUnitTokenPlay (s : GameState) (p : PlayerId) (batch : UnitTokenBatch)
    (pay : Option RunePool.Payment) (adds : List EffectAdd) (funding : EffectAddPolicy) :
    Option (GameState × List Event) := do
  let some payment := pay | some (enterUnitTokenBatch s p batch)
  let (card, _) :: rest := batch.entries | none
  let (funded, added) ← funding.applyAll s p adds
  let (paid, costs) ← payUnitTokenAccelerate funded p payment
  let (placed, plays) := enterUnitTokenBatch paid p { batch with entries := (card, true) :: rest }
  some (placed, added ++ costs ++ plays)

/-- Committing the completed token play preserves the structural invariants. -/
theorem finishUnitTokenPlay_safe {s : GameState} {p : PlayerId} {batch : UnitTokenBatch}
    {pay : Option RunePool.Payment} {adds : List EffectAdd} {funding : EffectAddPolicy}
    {r : GameState × List Event} (h : finishUnitTokenPlay s p batch pay adds funding = some r) :
    Safe s r.1 := by
  unfold finishUnitTokenPlay at h
  split at h
  · split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨funded, _⟩, hf, ⟨paid, _⟩, hp, rfl⟩ := h
      exact (funding.safe hf).trans
        ((payUnitTokenAccelerate_safe hp).trans (enterUnitTokenBatch_safe paid p _))
    · contradiction
  · obtain rfl := Option.some.inj h
    exact enterUnitTokenBatch_safe s p batch

/-- Ask which of the remaining replacement sequences to perform next (CR 372-373). -/
def beginUnitTokenEntries (batch : UnitTokenBatch) (replacements : List UnitTokenReplacement) : Effect :=
  match replacements with
  | [] => .planUnitTokenEntries batch (.substitute [] [] batch.entries.reverse [])
  | [next] => .planUnitTokenEntries batch (.apply next [])
  | _ => .eitherOf (EffectList.ofList (replacements.map (fun next =>
      Effect.planUnitTokenEntries batch (.apply next (replacements.erase next)))))

/-- Run all pending substitution choices as one uninterrupted sequence. The new definition
inherits the original entry instructions (CR 373.2, 375). -/
def unitTokenEntryPlan (s : GameState) (p : PlayerId) (batch : UnitTokenBatch)
    (substitutes : List CardId) (remaining chosen : List (CardId × Bool))
    (after : List UnitTokenReplacement) (funding : EffectAddPolicy) : Effect :=
  match remaining with
  | [] =>
    let original := batch.entries.head?.map Prod.fst
    let entries := if substitutes.isEmpty then chosen.reverse else
      let (replaced, ordinary) := chosen.reverse.partition (fun entry => some entry.1 != original)
      replaced ++ ordinary
    let planned := { batch with entries }
    if after.isEmpty then s.priceUnitToken p planned funding else beginUnitTokenEntries planned after
  | entry :: tail =>
    let replacements := substitutes.filter (· != entry.1)
    if replacements.isEmpty then
      .planUnitTokenEntries batch (.substitute substitutes tail (entry :: chosen) after)
    else
      let opts := (entry.1 :: replacements).map (fun card =>
        Effect.planUnitTokenEntries batch (.substitute substitutes tail ((card, entry.2) :: chosen) after))
      .eitherOf (EffectList.ofList opts)

/-- The replacement currently being applied can select an eligible entry or be declined. -/
def applyUnitTokenReplacement (batch : UnitTokenBatch) (replacement : UnitTokenReplacement)
    (after : List UnitTokenReplacement) : Effect :=
  match replacement with
  | .substitute cards => .planUnitTokenEntries batch (.substitute cards batch.entries [] after)
  | .duplicate src copy =>
    let options := (List.range batch.entries.length).map (fun i =>
      Effect.planUnitTokenEntries batch (.duplicate src copy (some i) after))
    let decline := Effect.planUnitTokenEntries batch (.duplicate src copy none after)
    .eitherOf (EffectList.ofList (options ++ [decline]))

/-- Add an extra play of the selected token, inheriting its destination, ready instruction and
linked follow-up. Both plays belonging to the replacement precede unaffected entries (CR 373.1, 375). -/
def duplicateUnitTokenEntry (batch : UnitTokenBatch) (src : ObjId) (copy : Option Timestamp)
    (entry : Option Nat) : UnitTokenBatch :=
  match entry.bind (fun i => (batch.entries[i]?).map (i, ·)) with
  | some (i, token) =>
    { batch with
      entries := token :: token :: batch.entries.eraseIdx i
      duplicatedBy := (src, copy) :: batch.duplicatedBy }
  | none => batch

/-- Resolve a decision in the token replacement plan before committing entry. -/
def nextUnitTokenPlan (s : GameState) (p : PlayerId) (batch : UnitTokenBatch) (funding : EffectAddPolicy) :
    UnitTokenPlan → Effect
  | .substitute cards remaining chosen after => unitTokenEntryPlan s p batch cards remaining chosen after funding
  | .apply replacement after => applyUnitTokenReplacement batch replacement after
  | .duplicate source copy entry after =>
    let planned := duplicateUnitTokenEntry batch source copy entry
    if after.isEmpty then s.priceUnitToken p planned funding else beginUnitTokenEntries planned after

/-- The legacy paths handle Gear and effects without a token replacement or new optional cost. -/
def unitTokenPrimStep (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (pr : Prim) (es : EffectList) : GameState × List Frame × List Event :=
  let replacements := s.unitTokenReplacements p
  let planned := if !replacements.isEmpty || (s.fxOf p).contains .nextUnitAccelerate then
    unitTokenBatchOf s p src env pr else none
  match planned with
  | some batch =>
    (s, [.run p src env (.cons (beginUnitTokenEntries batch replacements) es)], [])
  | none =>
    match applyPrim s p src env pr with
    | some (t, events) => (t, [.run p src env es], events)
    | none => (s, [.run p src env es], [.skipped src])

/-- Planning or resolving a token play preserves the structural invariants. -/
theorem unitTokenPrimStep_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env)
    (pr : Prim) (es : EffectList) : Safe s (unitTokenPrimStep s p src env pr es).1 := by
  unfold unitTokenPrimStep
  dsimp only
  split
  · exact Safe.refl s
  · split
    · rename_i t events happly
      exact applyPrim_safe (r := (t, events)) happly
    · exact Safe.refl s

/-- A token play continues with frames of the current play. -/
theorem unitTokenPrimStep_mem {s : GameState} {p : PlayerId} {src : ObjId} {env : Env}
    {pr : Prim} {es : EffectList} {f : Frame}
    (h : f ∈ (unitTokenPrimStep s p src env pr es).2.1) : f.isPlay = true := by
  unfold unitTokenPrimStep at h
  dsimp only at h
  split at h
  · cases List.mem_singleton.mp h
    rfl
  · split at h <;> cases List.mem_singleton.mp h <;> rfl

/-- Offer the death replacements before committing a permanent's additional play cost. -/
def permanentDeathCostChoice (s : GameState) (card : ObjId) (plan : ReducedPermanentPlay) :
    Option (ObjId × PlayerId × Effect × Effect) := do
  let d ← s.cardDef? card
  let (cost, _) ← d.playExtra
  let unit ← plan.extraObject
  if cost.kills then s.deathReplacementChoice unit else none

/-- Execute a primitive instruction that may schedule further resolution or a decision. -/
def runPrimEffect (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (pr : Prim)
    (es : EffectList) (funding : EffectAddPolicy) : GameState × List Frame × List Event :=
  let skip : GameState × List Frame × List Event := (s, [.run p src env es], [Event.skipped src])
  match pr with
  | move@(.move ..) | move@(.swapPlaces ..) =>
    moveEffectStep s p src env move .nop es
  | .playUnitToken name =>
    match s.tokenCard name with
    | some c =>
      let options := (s.unitTokenDestinations p c).map (fun dest => Effect.prim (.playUnitTokenAt name dest))
      (s, [.run p src env (.cons (.eitherOf (EffectList.ofList options)) es)], [])
    | none => skip
  | .burn who n => burnEffect s p src env who n es
  | .burnWithUnitTrigger n idx => burnEffect s p src env .you n es (some idx)
  | .predict n =>
    match n.evalS s p src env with
    | some count =>
      match (s.zone (.player p .mainDeck)).take count with
      | [] => (s, [.run p src env es], [])
      | c :: cs =>
        (s, [.predict p count c cs [] [], .run p src env es], (c :: cs).map (Event.lookedAt p))
    | none => skip
  | .draw sel n =>
    match sel.resolve s p env, n.evalS s p src env with
    | some ps, some k => (s, ps.map (fun q => Frame.draw q k) ++ [.run p src env es], [])
    | _, _ => skip
  | .reveal sel =>
    -- the player looks at the top card first, and may recycle it, and then the cards are revealed
    if s.lookFirst p env sel then
      (s, [.run p src env (.cons (.prim (.lookTop 1)) (.cons (.may (.prim (.recycleTop .you)))
        (.cons (.prim (.revealNow sel)) es)))], [])
    else
      match applyPrim s p src env (.reveal sel) with
      | some r => (r.1, [.run p src env es], r.2)
      | none => skip
  | .revealTop n =>
    -- the player looks at the top card first, and may recycle it, and then the cards are revealed
    if s.passiveSources.any (fun g => (s.obj? g).any (·.controller == p) &&
        (s.activeMods g).contains .lookBeforeReveal) then
      (s, [.run p src env (.cons (.prim (.lookTop 1)) (.cons (.may (.prim (.recycleTop .you)))
        (.cons (.prim (.revealTopNow n)) es)))], [])
    else
      match applyPrim s p src env (.revealTop n) with
      | some r => (r.1, [.run p src env es], r.2)
      | none => skip
  | .castInline sel => castInlineStep s p src env sel es funding
  | pr@(.create ..) | pr@(.createAt ..) | pr@(.createAtPrev ..) |
    pr@(.playUnitTokenAt ..) | pr@(.cloneToken ..) =>
    unitTokenPrimStep s p src env pr es
  | .kill sel => killEffectStep s p src env sel none es
  | .banishReplay sel replay =>
    let units := (sel.eval s p src env).getD []
    let replays := EffectList.ofList (units.map (fun unit => .banishForReplay unit replay))
    (s, [.run p src env (replays.append es)], [])
  | .playReduced sel less dest =>
    match castReducedStep s p src env sel less dest es funding with
    | some r => r
    | none =>
      match permanentPlayEffects s p src env (.playReduced sel less dest) with
      | some (context, plays) => (s, [.run p src context plays, .run p src env es], [])
      | none =>
        match applyPrim s p src env (.playReduced sel less dest) with
        | some r => (r.1, [.run p src env es], r.2)
        | none => skip
  | .play sel =>
    match playSpellStep s p src env sel es funding with
    | some r => r
    | none =>
      match permanentPlayEffects s p src env (.play sel) with
      | some (context, plays) => (s, [.run p src context plays, .run p src env es], [])
      | none =>
        match applyPrim s p src env (.play sel) with
        | some r => (r.1, [.run p src env es], r.2)
        | none => skip
  | .discard sel n =>
    match sel.resolve s p env, n.evalS s p src env with
    | some ps, some k => (s, ps.map (fun q => Frame.discard q k) ++ [.run p src env es], [])
    | _, _ => skip
  | pr =>
    match effectDamageBatch? s p src env pr with
    | some batch => (s, [.run p src env (.cons (.resolveEffectDamage batch none) es)], [])
    | none =>
      match permanentPlayEffects s p src env pr with
      | some (context, plays) => (s, [.run p src context plays, .run p src env es], [])
      | none =>
        match applyPrim s p src env pr with
        | some r => (r.1, attachmentReplacementFrames r.1 r.2 ++ [.run p src env es], r.2)
        | none => skip

set_option maxHeartbeats 1200000 in
/-- Executing a primitive instruction preserves the structural invariants. -/
theorem runPrimEffect_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (pr : Prim)
    (es : EffectList) (funding : EffectAddPolicy) : Safe s (runPrimEffect s p src env pr es funding).1 := by
  unfold runPrimEffect
  split <;> (try split) <;> (try split) <;> (try split) <;> first
    | exact Safe.refl s
    | exact moveEffectStep_safe s p src env _ _ es _
    | exact burnEffect_safe s p src env _ _ es _
    | exact castInlineStep_safe s p src env _ es funding
    | exact unitTokenPrimStep_safe s p src env _ es
    | exact killEffectStep_safe s p src env _ _ es
    | exact playSpellStep_safe (by assumption)
    | exact castReducedStep_safe (by assumption)
    | exact applyPrim_safe (by assumption)

/-- Execute one effect and prepare the frames that continue it. -/
def runEffect1 (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) (funding : EffectAddPolicy) : GameState × List Frame × List Event :=
  let skip : GameState × List Frame × List Event := (s, [.run p src env es], [Event.skipped src])
  let linked (a : Prim) (body : Effect) :=
    let r := linkedAction s p src env a
    (r.1, [.run p src env (if r.2.1 then .cons body es else es)], r.2.2)
  match e with
  | .nop => (s, [.run p src env es], [])
  | .addReservedLegend => (s, [addReservedLegendFrame s p src env es], [])
  | .addReservedLegendPicked =>
    match env.lookup pickVar with
    | some (.obj legend) => (s, [.run p src env (.cons (.addReservedLegendChosen legend) es)], [])
    | _ => skip
  | .addReservedLegendChosen legend =>
    let result := addReservedLegend s p src legend
    (result.1, [.run p src env es], result.2)
  | .animateGear =>
    match env.slots.head? with
    | some (.obj gear) => (animateGearObject s p src gear, [.run p src env es], [])
    | _ => skip
  | .playUnitTokensThen name count place ready index target =>
    match linkedUnitTokenBatch s p src env name count place ready index target with
    | some batch => (s, [.run p src env (.cons (beginUnitTokenEntries batch (s.unitTokenReplacements p)) es)], [])
    | none => skip
  | .planUnitTokenEntries batch plan =>
    (s, [.run p src env (.cons (nextUnitTokenPlan s p batch funding plan) es)], [])
  | .fundTokenAccelerate batch payment adds =>
    let opts := fundUnitTokenOptions s p batch ⟨payment.1, payment.2⟩ adds funding
    (s, [.run p src env (.cons (.eitherOf (EffectList.ofList opts)) es)], [])
  | .finishUnitTokens batch pay adds =>
    match finishUnitTokenPlay s p batch (pay.map fun (energy, power) => ⟨energy, power⟩) adds funding with
    | some r => (r.1, [.run p src env es], r.2)
    | none => skip
  | .seq l => (s, [.run p src env (l.append es)], [])
  | .bind v a e' =>
    match a.evalS s p src env with
    | some k => (s, [.run p src (env.bind v (.int k)) (.cons e' .nil), .run p src env es], [])
    | none => skip
  | .ifThen c t e' =>
    match c.eval s p src (env.withMight s.mightTable) with
    | some b => (s, [.run p src env (.cons (if b then t else e') es)], [])
    | none => skip
  | .fillFromPick i =>
    -- the object that was chosen becomes slot `i`
    match env.lookup pickVar with
    | some v => (s, [.run p src { env with slots := env.slots.set i v } es], [])
    | none => skip
  | .preventNext sel amount .thisTurn =>
    match amount.evalS s p src env with
    | some (k + 1) =>
      (s, [.run p src env (.cons (.prim (.markOn sel (.preventDamage (k + 1)))) es)], [])
    | _ => (s, [.run p src env es], [])
  | .retainTargetSet groups => (s, [retainTargetSetFrame p src env groups es], [])
  | .remakeSpellChoices spell =>
    (s, [remakeSpellChoicesFrame s p src env spell es], [])
  | .resolveSpellExecution pick targets =>
    (s, spellExecutionFrames s p src env pick targets ++ [.run p src env es], [])
  | .setSpellChoices spell pick targets =>
    let updated := s.modObj spell fun o =>
      let newPick := match o.spellPick.optionalCosts with
        | some (printed, repeats) => .withCosts pick printed repeats
        | none => if pick.hasExecutionChoices then .withCosts pick o.paid o.extraPaid else pick
      { o with targets, spellPick := newPick, targetPlayer := pick.playerTarget }
    (updated, [.run p src env es], targets.map (Event.chosenBySpell p))
  | .moveChoosing unit home fs afterMove afterNegatedMove =>
    let chosen := chosenMove s p src env unit home fs afterMove afterNegatedMove
    (s, [.run p src chosen.1 (.cons chosen.2 es)], [])
  | .forceMoveToBattlefield who destination =>
    (s, [forceMoveToBattlefieldFrame s p src env who destination es], [])
  | .equipWithCost gear recipient less =>
    (s, [equipWithCostFrame s p src env gear recipient less es], [])
  | .grantNumericKeyword objects keyword amount duration =>
    match amount.evalS s p src env with
    | some n => (s, [.run p src env
        (.cons (.grant objects (.keyword .it ⟨keyword, .amount n⟩) duration) es)], [])
    | none => skip
  | .pickOwn place fs body =>
    (s, [.run p src env (.cons (.collectOwnPicks p s.pickOrder place fs body false) es)], [])
  | .collectOwnPicks controller players place fs body capture =>
    (s, [collectOwnPicksFrame s controller src env players place fs body capture es], [])
  | .forEach sel body =>
    match sel.eval s p src env with
    | some ids =>
      (s, ids.map (fun id => Frame.run p src { env with it := some id } (.cons body .nil)) ++
        [.run p src env es], [])
    | none => skip
  | .repeatN n e' =>
    match n.evalS s p src env with
    | some k => (s, [.run p src env ((EffectList.replicate k e').append es)], [])
    | none => skip
  | .eachPlayer who body =>
    match (match who with
      | .controllerOf i =>
        -- the controller of the object chosen at the slot
        match env.slots[i]? with
        | some (.obj o) =>
          (s.obj? o).bind fun x =>
            if s.departures.seats.contains x.controller then none else some [x.controller]
        | _ => none
      | _ => who.resolve s p env : Option (List PlayerId)) with
    | some ps =>
      let playerEnv := { env with effectController := env.effectController <|> some p }
      (s, ps.map (fun q => Frame.run q src playerEnv (.cons body .nil)) ++ [.run p src env es], [])
    | none => skip
  | .revealHand who body =>
    match who.resolve s p env with
    | some ps =>
      let hands := ps.map (fun q => (q, s.zone (.player q .hand)))
      let known := { env with revealedCards := hands.flatMap Prod.snd ++ env.revealedCards }
      (s, [.run p src known (.cons body .nil), .run p src env es],
        hands.map (fun (q, cards) => .handRevealed q cards))
    | none => skip
  | .revealDeckTops who body =>
    match who.resolve s p env with
    | some players =>
      let tops := players.filterMap (fun q =>
        (s.zone (.player q .mainDeck)).head?.map (fun id => (q, id)))
      let cards := tops.map Prod.snd
      let known := { env with lookedCards := cards, revealedCards := cards }
      (s, [.run p src known (.cons body .nil), .run p src env es],
        tops.map (fun (q, id) => .revealed q id))
    | none => skip
  | .guessCardType who unit gear spell =>
    match who.resolve s p env with
    | some [guesser] => (s, [.guessCardType guesser p src env unit gear spell es], [])
    | _ => skip
  | .markTriggeredAdd idx =>
    (s.modObj src (fun o => o.noteAbilityUse idx env.abilityCopyStamp), [.run p src env es], [])
  | .nameCard kind =>
    match s.nameableCards kind with
    | first :: more => (s, [.nameCard p src env first more es], [])
    | [] => skip
  | .rememberNamedCard card =>
    (s.modObj src (fun o => { o with namedCard := some card }), [.run p src env es],
      [.namedCard p src card])
  | .lookAtTop n body =>
    let cards := (s.zone (.player p .mainDeck)).take n
    (s, [.run p src { env with lookedCards := cards } (.cons body .nil), .run p src env es],
      cards.map (.lookedAt p))
  | .banishAndPlayLooked less fs =>
    match lookedPlayCandidates s p src env less fs funding with
    | first :: more => (s, [.mayDo p src env (.chooseLookedToPlay less first more) es], [])
    | [] => (s, [.run p src env es], [])
  | .chooseLookedToPlay less first more =>
    (s, [.pickDo p src env first more (.banishLookedForPlay less) es], [])
  | .banishLookedForPlay less => banishLookedStep s p src env less es funding
  | .mayPlayCard sel price =>
    let cards := effectPlayCandidates s p src env sel
    (s, [.run p src env (.cons (.offerNextCardPlay cards 1 price) es)], [])
  | .playCard sel price baseOnly =>
    (s, [requiredCardPlayFrame s p src env sel price funding es baseOnly], [])
  | .banishTopForPlay =>
    let result := banishTopForPlay s p
    (result.1, [.run p src env es], result.2)
  | .banishAndPlayCard sel price =>
    match sel.eval s p src env with
    | some [id] =>
      let banished := banishObj p s id
      let next := match banishedPlayId banished.2 with
        | some card =>
          let context := env.bindPick card false
          [.run p src context (.cons (.playCard (.var pickVar) price) .nil), .run p src env es]
        | none => [.run p src env es]
      (banished.1, next, banished.2)
    | _ => skip
  | .playSelfFromTrash cost exit =>
    if (s.zone (.player p .trash)).contains src then
      let price := EffectPlayPrice.alternateBase cost
      if (s.cardDef? src).any (·.hasType .spell) then
        castLimitedStep s p src env src price exit es funding
      else
        let options := effectPermanentFinalizations s p src env price funding
        (s, [.run p src env (.cons options es)], [])
    else skip
  | .mayPlayPermanents sel maximum price =>
    let cards := (effectPlayCandidates s p src env sel).filter (fun card =>
      (s.cardDef? card).any (fun d => !d.hasType .spell && (d.hasType .unit || d.hasType .gear)))
    (s, [.run p src env (.cons (.offerNextCardPlay cards maximum price) es)], [])
  | .offerNextCardPlay cards remaining price =>
    if remaining == 0 then (s, [.run p src env es], []) else
      match cards.filter (fun card => effectCardPlayable s p card env price funding) with
      | [] => (s, [.run p src env es], [])
      | first :: others =>
        (s, [.mayDo p src env (.chooseOfferedPlay cards remaining price first others) es], [])
  | .chooseOfferedPlay cards remaining price first others =>
    (s, [.pickDo p src env first others (.playOfferedCard cards remaining price) es], [])
  | .playOfferedCard cards remaining price baseOnly =>
    match env.lookup pickVar with
    | some (.obj card) =>
      if (s.cardDef? card).any (·.hasType .spell) then
        castLimitedStep s p src env card price .normal es funding
      else
        let options := effectPermanentFinalizations s p card env price funding baseOnly
        let next := if baseOnly then es else
          EffectList.cons (.afterOfferedPlay card (cards.erase card) remaining price) es
        (s, [.run p src env (.cons options next)], [])
    | _ => skip
  | .afterOfferedPlay card cards remaining price =>
    let count := if env.lookup pickVar == some (.obj card) then remaining else remaining - 1
    (s, [.run p src env (.cons (.offerNextCardPlay cards count price) es)], [])
  | .planPermanentPlay card terms =>
    match permanentPlayPlans s p card terms with
    | [] => skip
    | plans =>
      let options := plans.map (.finishReducedPermanent card terms)
      let decline := if plans.all (fun plan => !plan.battlefieldFees.isEmpty) then [.nop] else []
      (s, [.run p src env (.cons (.eitherOf (EffectList.ofList (options ++ decline))) es)], [])
  | .banishAndReplayGroup =>
    let ids := env.slots.filterMap (fun | .obj id => some id | _ => none)
    let (t, replays, events) := banishReplayGroup p ids s
    let ordered := s.pickOrder.flatMap (fun owner => replays.filter (fun replay => replay.1 == owner))
    (t, [.run p src env (.cons (.orderBanishReplays ordered []) es)], events)
  | .orderBanishReplays remaining ordered => orderBanishReplayFrames p src env remaining ordered es s
  | .recordBanishReplay controller remaining ordered =>
    match remaining.find? (fun (_, card, _) => env.lookup pickVar == some (.obj card)) with
    | some choice =>
      let next := Effect.orderBanishReplays (remaining.erase choice) (choice :: ordered)
      (s, [.run controller src env (.cons next es)], [])
    | none => skip
  | .planBanishReplay card location =>
    let requirements := [none :: location.toList.map some] ++ env.hiddenPlayRequirements
    let terms : EffectPlayTerms := { price := .ignoreBase, requirements }
    (s, [.run p src env (.cons (fundedPermanentOptions s p card terms funding) es)], [])
  | .cancelBanishReplay card =>
    let canceled := cancelBanishReplay s p card
    (canceled.1, [.run p src env es], canceled.2)
  | .banishForReplay id replay =>
    let banished := banishObj p s id
    (banished.1, replayFrames s p src env id replay banished.2 es, banished.2)
  | .finishReducedPermanent card terms plan =>
    if (permanentPlayPlans s p card terms).contains plan then
      match permanentDeathCostChoice s card plan with
      | some (victim, controller, first, other) =>
        (s, [.eitherDo controller victim {} first other .nil, .run p src env (.cons e es)], [])
      | none =>
        match applyReducedPermanent s p card plan with
        | some (t, entered, events) => (t, [.run p src (env.bind pickVar (.obj entered)) es], events)
        | none => skip
    else skip
  | .finishFundedPermanent card terms plan adds =>
    match permanentDeathCostChoice s card plan with
    | some (victim, controller, first, other) =>
      (s, [.eitherDo controller victim {} first other .nil, .run p src env (.cons e es)], [])
    | none =>
      match finishFundedPermanentPlay s p card terms plan adds funding with
      | some (t, entered, events) => (t, [.run p src (env.bind pickVar (.obj entered)) es], events)
      | none => skip
  | .fundPermanentFromEffect card terms plan adds =>
    let choices := fundPermanentOptions s p card terms plan adds funding
    (s, [.run p src env (.cons (.eitherOf (EffectList.ofList choices)) es)], [])
  | .recycleLooked => recycleLookedStep s p src env es
  | .recycleRunes =>
    let runes := s.inPlay.filter (fun id =>
      (s.cardDef? id).any (·.hasType .rune) && (s.obj? id).any (·.controller == p))
    let groups := s.players.map (fun owner =>
      (owner, runes.filter (fun id => (s.obj? id).any (·.owner == owner))))
    (s, [.run p src env (.cons (.orderRuneRecycle groups []) .nil), .run p src env es], [])
  | .orderRuneRecycle groups picked =>
    match groups with
    | [] =>
      let recycled := recycleList picked.reverse s
      (recycled.1, [.run p src env es], recycled.2)
    | (_, []) :: rest =>
      (s, [.run p src env (.cons (.orderRuneRecycle rest picked) es)], [])
    | (_, [last]) :: rest =>
      (s, [.run p src env (.cons (.orderRuneRecycle rest (last :: picked)) es)], [])
    | (owner, first :: second :: rest) :: later =>
      let resume := Effect.recordRuneRecycle (first :: second :: rest) later picked
      (s, [.pickDo owner src env first (second :: rest) resume es], [])
  | .recordRuneRecycle remaining later picked =>
    match env.lookup pickVar with
    | some (.obj id) =>
      if remaining.contains id then
        (s, [.run p src env (.cons (.orderRuneRecycle ((p, remaining.erase id) :: later)
          (id :: picked)) es)], [])
      else skip
    | _ => skip
  | .may e' =>
    if (requiredPlayCandidates s p src env e' funding).any List.isEmpty then skip
    else (s, [.mayDo p src env e' es], [])
  | .doThen (.prim (.banish sel)) body => linked (.banish sel) body
  | .doThen (.prim (.disempower sel)) body => linked (.disempower sel) body
  | .doThen (.prim (.exhaust sel)) body => linked (.exhaust sel) body
  | .doThen (.prim (.spendBuff sel)) body => linked (.spendBuff sel) body
  | .doThen (.prim (move@(.move ..))) body => moveEffectStep s p src env move body es
  | .moveAfterFee move body => moveEffectStep s p src env move body es true
  | .payThen cost body gearPower =>
    match resolutionPayments s p src cost gearPower with
    | [] => skip
    | [(_, pool)] =>
      (if gearPower then s.setPoolFor p src pool else s.setPool p pool,
        [.run p src env (.cons body es)], [])
    | first :: second :: more =>
      let choices := (first :: second :: more).map (fun plan => Effect.paySelected plan.1 body gearPower)
      (s, [.run p src env (.cons (.eitherOf (EffectList.ofList choices)) es)], [])
  | .paySelected cost body gearPower =>
    match spendResolutionPayment s p src cost gearPower with
    | none => skip
    | some pool =>
      (if gearPower then s.setPoolFor p src pool else s.setPool p pool,
        [.run p src env (.cons body es)], [])
  | .eitherOf .nil => skip
  | .eitherOf (.cons a rest) =>
    -- the player chooses between the first effect ("yes") and the others ("no"), and so on
    match rest with
    | .nil => (s, [.run p src env (.cons a es)], [])
    | .cons b .nil => (s, [.eitherDo p src env a b es], [])
    | r => (s, [.eitherDo p src env a (.eitherOf r) es], [])
  | .finalizeLimitedSpell card => finalizeLimitedStep s p src env card es funding
  | .fundLimitedSpell card plan adds =>
    let choices := fundLimitedOptions s p card plan adds funding
    (s, [.run p src env (.cons (.eitherOf (EffectList.ofList choices)) es)], [])
  | .cancelLimitedSpell card => cancelLimitedStep s p src env card es
  | .finishLimitedSpell card plan adds =>
    match (s.playDeathCost card plan.targets plan.pick).bind (fun unit => s.deathReplacementChoice unit) with
    | some (victim, controller, first, other) =>
      (s, [.eitherDo controller victim {} first other .nil, .run p src env (.cons e es)], [])
    | none =>
      match commitLimitedSpell s p card plan adds funding with
      | some (t, events) => (t, [.chainPass p 0, .run p src env es], events)
      | none => cancelLimitedStep s p src env card es
  | .splitDamage targets total =>
    match targets.eval s p src env with
    | some (first :: others) =>
      let available := total + s.bonusOn p src first env.sourceCard
      let choices := (damageDivisions (first :: others) available).map Effect.applySplitDamage
      (s, [.run p src env (.cons (.eitherOf (EffectList.ofList choices)) es)], [])
    | _ => skip
  | .applySplitDamage hits =>
    if s.damageOff then (s, [.run p src env es], []) else
      let batch : EffectDamageBatch := {
        controller := some (env.effectController.getD p)
        incoming := hits }
      (s, [.run p src env (.cons (.resolveEffectDamage batch none) es)], [])
  | .resolveEffectDamage batch hit => resolveEffectDamageStep s p src env batch hit es
  | .chooseDamageReplacement batch hit replacement =>
    let (next, damage) := chooseEffectDamage batch hit replacement
    (s, [.run p src env (.cons (.resolveEffectDamage next (some damage)) es)], [])
  | .orderCombatDamage target chosen remaining =>
    orderCombatDamageStep s p src env target chosen remaining es
  | .chooseDeathBanisher unit banisher =>
    (s.addTurnFxOn banisher unit .chosenDeathBanisher, [.run p src env es], [])
  | .chooseDeathGear unit gear =>
    (s.addTurnFxOn p unit (.chosenDeathGear gear), [.run p src env es], [])
  | .chooseDeathFree unit source =>
    (s.addTurnFxOn p unit (.chosenDeathFree source), [.run p src env es], [])
  | .recordDeathSacrifice unit cost =>
    (s.addTurnFxOn p unit (.deathSacrificeChoice cost), [.run p src env es], [])
  | .recordDeathOrder group unit =>
    (s.addTurnFxOn p unit (.deathOrder group), [.run p src env es], [])
  | .recordDeathReselection group earlier unit choice =>
    (s.addTurnFxOn p unit (.deathReselection group earlier choice), [.run p src env es], [])
  | .recordNestedDeathDecision root used unit choice groupScope =>
    (s.addTurnFxOn p unit (.nestedDeathDecision root used choice groupScope), [.run p src env es], [])
  | .endCombatDamage excess =>
    (recordCombatDamage s p excess, [.run p src env es], [])
  | .killThenAtEnd targets index => killEffectStep s p src env targets (some index) es
  | .killThenForController slot body =>
    killEffectStep s p src env (.slot slot) none es (some ⟨slot, body, .forController⟩)
  | .killThenIfKilled slot body =>
    killEffectStep s p src env (.slot slot) none es (some ⟨slot, body, .ifKilled⟩)
  | .grant sel m d =>
    match applyGrant s p src env sel m d with
    | some r => (r.1, [.run p src env es], r.2)
    | none => skip
  | .prim pr => runPrimEffect s p src env pr es funding
  | _ => skip

set_option maxHeartbeats 2400000 in
/-- Doing an effect, but not a choice, is a safe change of the state. -/
theorem runEffect1_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) (funding : EffectAddPolicy) : Safe s (runEffect1 s p src env e es funding).1 := by
  unfold runEffect1
  split <;> (try split) <;> (try split) <;> (try split) <;> first
    | exact Safe.refl s
    | exact runPrimEffect_safe s p src env _ es funding
    | exact Safe.modObj s src (fun _ => rfl) (fun _ => rfl)
    | exact Safe.modObj s _ (fun _ => rfl) (fun _ => rfl)
    | exact addReservedLegend_safe s p src _
    | exact castLimitedStep_safe s p src env _ _ _ es funding
    | exact finalizeLimitedStep_safe s p src env _ es funding
    | exact cancelLimitedStep_safe s p src env _ es
    | exact resolveEffectDamageStep_safe s p src env _ _ es
    | exact orderCombatDamageStep_safe s p src env _ _ _ es
    | exact killEffectStep_safe s p src env _ _ es
    | exact animateGearObject_safe s p src _
    | exact finishUnitTokenPlay_safe (by assumption)
    | exact moveEffectStep_safe s p src env _ _ es _
    | exact recordCombatDamage_safe s p _
    | exact addTurnFxOn_safe s _ _ _
    | exact commitLimitedSpell_safe (by assumption)
    | exact linkedAction_safe s p src env _
    | exact banishObj_safe p s _
    | exact banishReplayGroup_safe p _ s
    | exact orderBanishReplayFrames_safe p src env _ _ es s
    | exact cancelBanishReplay_safe s p _
    | exact banishTopForPlay_safe s p
    | exact banishLookedStep_safe s p src env _ es funding
    | exact recycleLookedStep_safe s p src env es
    | exact recycleList_safe _ s
    | exact setPoolFor_safe s p src _
    | exact setPool_safe s p _
    | (exact applyReducedPermanent_safe (by assumption))
    | (exact finishFundedPermanentPlay_safe (by assumption))
    | exact applyGrant_safe (by assumption)

/-- Do the first effect of `e :: es`: the new state, the frames that replace the `run` frame, and
the events. An instruction that cannot be done is skipped (design.md §7.1). An effect that names an
object to choose while it resolves ("kill a gear") asks the player when there is more than one to
choose from, and goes on with the only one when there is one (CR 355). -/
def runEffect (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) (funding : EffectAddPolicy) : GameState × List Frame × List Event :=
  match e.pickSel? with
  | some (.pick _ side place fs) =>
    -- A linked first action is a cost. Its pick is not a target (CR 355.10.c.1).
    match requiredPlayCandidates s p src env e funding <|>
        s.pickCandidates p src env side place fs (!e.isLinkedCost) with
    | some [o] =>
      match e with
      | .chooseObject .. => (s, [.pickDo p src env o [] e.withPick es], [])
      | _ =>
        (s, [.run p src (env.bindPick o (e.pickIsTarget s o)) (.cons e.withPick es)],
          e.pickEvents s p src o)
    | some (o :: o2 :: more) => (s, [.pickDo p src env o (o2 :: more) e.withPick es], [])
    | _ => (s, [.run p src env es], [Event.skipped src])
  | _ => runEffect1 s p src env e es funding

/-- Doing an effect is a safe change of the state. -/
theorem runEffect_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) (funding : EffectAddPolicy) : Safe s (runEffect s p src env e es funding).1 := by
  unfold runEffect
  split
  · split
    · split <;> exact Safe.refl s
    · exact Safe.refl s
    · exact Safe.refl s
  · exact runEffect1_safe s p src env e es funding

/-- The ability of the card identified by an item on the Chain (CR 337). -/
def abilityAt (s : GameState) (card : CardId) (idx : Nat) : Option Ability :=
  (s.cards.find? card).bind (fun d => d.allAbilities[idx]?)

/-- The choices and body of an ability that can go on the Chain. -/
def Ability.effectDef : Ability → Option EffectDef
  | .activated _ _ body _ | .triggered _ body _ => some body
  | _ => none

/-- The effect of the ability of a card: its choices and its body. -/
def abilityDef (s : GameState) (card : CardId) (idx : Nat) : Option EffectDef :=
  (abilityAt s card idx).bind Ability.effectDef

/-- The frames that resolve an item of the Chain that is not a card: an ability runs its effect for
its controller, with the objects chosen as the slots, and then it leaves the Chain (CR 340). -/
def itemFrames (s : GameState) (item : ObjId) (o : Object) (rest : List Frame) : List Frame :=
  match o.kind with
  | .chainAbility card idx src =>
    let ability := (o.triggerKeyword.bind CardDef.keywordTrigger) <|>
      (match o.activationGrant with
        | some grant => s.grantedActivation grant
        | none => abilityAt s card idx)
    let definition := (ability.bind Ability.effectDef).bind (·.forPick o.spellPick)
    let definition := definition.map (fun e =>
      { e with choices := e.choices.map (Choice.withTriggerEvent o.eventBattlefields o.eventObjects) })
    let recheck := o.spellPick != .plain || definition.any (fun e =>
      e.recheckTargets || (!e.choices.isEmpty && e.choices.all (fun
        | .target .one .. | .target (.upTo 1) .. => true
        | _ => false)))
    let subject := o.triggerSubject.toList
    let targets := if o.spellPick == .plain then o.targets.take (o.targets.length - subject.length)
      else o.targets
    let slots := if recheck then recheckedSlots s o.controller src targets definition ++
      subject.map Value.obj else slotValues o.targets definition
    let targetObjs := match ability with
      | some (.activated costs _ _ _) =>
        if costs.any (fun | .killFriendly .. => true | _ => false) then targets.dropLast
        else targets
      | _ => targets
    let hiddenPlayLocation := match ability, s.obj? src with
      | some (.activated costs _ _ _), some source =>
        if costs.contains .fromHidden then source.hiddenAt else none
      | some (.triggered trigger _ _), some source =>
        if trigger.event == .play && trigger.subject == .self && source.fromHidden then source.loc
        else none
      | _, _ => none
    let env : Env := {
      slots
      targetObjs
      playerTargets := o.targetPlayer.toList
      hiddenPlayLocation
      sourceCard := some ((o.activationGrant.filter (·.copyStamp.isSome)).map (·.card) |>.getD card)
      abilityCopyStamp := o.abilityCopyStamp
      eventBattlefields := o.eventBattlefields
      eventObjects := o.eventObjects
      shownOff := o.shownOff
      eventAmount := o.eventAmount }
    let body := match definition with
      | some e => e.recheckTargetGroup s o.controller src o.targets (.cons e.body .nil)
      | none => .nil
    .run o.controller src env body :: .finishSpell item :: rest
  | _ => .finishSpell item :: rest

/-- The effects that choose the targets of an effect again: one for each target of exactly one
object (the others keep what they were) (CR 820). -/
def EffectDef.refills (e : EffectDef) : List Effect :=
  let rec go : List Choice → Nat → List Effect
    | [], _ => []
    | .target .one side place fs :: cs, i =>
      .fillSlot i (Selector.pick .one side place fs) :: go cs (i + 1)
    | .target _ _ _ _ :: cs, i => go cs (i + 1)
    | _ :: cs, i => go cs i
  go e.choices 0

/-- What a repeated effect does after the first time: the targets are chosen again, then the effect
is done (CR 820). -/
def EffectDef.repeats (e : EffectDef) : Nat → EffectList
  | 0 => .nil
  | m + 1 => (EffectList.ofList e.refills).append (.cons e.body (e.repeats m))

/-- An effect done `n` times: the first time with the targets chosen when the Spell was played, the
others with the targets chosen again (CR 820). -/
def EffectDef.executions (e : EffectDef) (n : Nat) : EffectList :=
  match n with
  | 0 => .nil
  | m + 1 => .cons e.body (e.repeats m)

/-- The frames that resolve the item on top of the Chain (CR 340): run its effect, then it leaves
the Chain (a Spell goes to the Trash, an ability ceases to exist). Nothing to resolve when the
Chain is empty. -/
def resolveFrames (s : GameState) (rest : List Frame) : List Frame :=
  match s.zone .chain with
  | item :: _ =>
    match s.obj? item, s.cardDef? item with
    | some o, some d =>
      if o.spellPick.hasExecutionChoices then
        (o.spellPick.executions o.targets).map (fun (pick, targets) =>
          .run o.controller item { hiddenPlayLocation := o.hiddenAt, shownOff := o.shownOff }
            (.cons (.resolveSpellExecution pick targets) .nil)) ++ (.finishSpell item :: rest)
      else
        let definition := d.spellForPick o.spellPick
        .run o.controller item {
          slots := finalizedSlots s o.controller item o.targets definition o.spellPick
          targetObjs := o.targets
          hiddenPlayLocation := o.hiddenAt
          shownOff := o.shownOff
          playerTargets := if definition.any (fun e => s.spellPlayerTargetOk o.controller e o.spellPick)
            then o.targetPlayer.toList else [] }
          (match definition with
            | some e =>
              -- once, and once more for each Repeat that was paid (CR 820)
              e.recheckTargetGroup s o.controller item o.targets
                (e.executions (1 + o.extraPaid))
            | none => .nil) :: .finishSpell item :: rest
    | some o, none => itemFrames s item o rest
    | none, _ => .finishSpell item :: rest
  | [] => rest

/-- Finish a Chain item: a Spell moves to its destination and an ability ceases to exist
(CR 359.3.d, 829.1.b.1). Nothing happens if it has already left the Chain. -/
def finishItem (s : GameState) (item : ObjId) : GameState × List Event :=
  match s.obj? item with
  | some o =>
    if item ∈ s.zone .chain then
      match o.kind with
      | .chainAbility .. =>
        match removeObj s item with
        | some s2 => (s2, [])
        | none => (s, [])
      | _ =>
        match moveObj s item (s.chainDestination item o .trash) with
        | some r =>
          let es := s.chainExitEvents o item r.2 .trash
          (r.1, es ++ spellCompletion s item es)
        | none => (s, [])
    else (s, [])
  | none => (s, [])

/-- Follow a completed play to its new object and Recycle it if the limited Play requires it.
A countered Spell has no resolution here (CR 420.4.a.1). -/
def finishedItemFrames (s : GameState) (item : ObjId) (r : GameState × List Event) : List Frame :=
  let recycle := (s.obj? item).toList.flatMap (fun o =>
    if o.limitedSpellExit != .recycle then [] else
    r.2.findSome? (fun
      | .moved old next _ => if old == item then some next else none
      | _ => none) |>.toList.map (fun next =>
        Frame.run o.owner next {} (.cons (.prim (.recycle .self)) .nil)))
  recycle ++ .cleanup :: afterItem r.1

/-- Recycling, Cleanup and continuing the Chain all consist of play frames. -/
theorem finishedItemFrames_mem {s : GameState} {item : ObjId} {r : GameState × List Event}
    {f : Frame} (hf : f ∈ finishedItemFrames s item r) : f.isPlay = true := by
  unfold finishedItemFrames at hf
  rcases List.mem_append.mp hf with hr | hn
  · obtain ⟨o, -, ho⟩ := List.mem_flatMap.mp hr
    split at ho
    · simp at ho
    · obtain ⟨next, -, rfl⟩ := List.mem_map.mp ho
      rfl
  · rcases List.mem_cons.mp hn with rfl | hn
    · rfl
    · exact afterItem_mem hn

/-- Finishing an item either changes nothing, moves a Spell, or removes an ability. -/
theorem finishItem_cases (s : GameState) (item : ObjId) :
    (finishItem s item).1 = s ∨
      (∃ o s2 id', s.obj? item = some o ∧ item ∈ s.zone .chain ∧
        moveObj s item (s.chainDestination item o .trash) = some (s2, id') ∧
          (finishItem s item).1 = s2) ∨
      (∃ o s2, s.obj? item = some o ∧ item ∈ s.zone .chain ∧ o.kind.phys? = none ∧
          removeObj s item = some s2 ∧ (finishItem s item).1 = s2) := by
  unfold finishItem
  split
  · rename_i o ho
    split
    · rename_i hc
      split
      · rename_i card idx src hk
        split
        · rename_i s2 hr
          exact Or.inr (Or.inr ⟨o, s2, ho, hc, by rw [hk]; rfl, hr, rfl⟩)
        · exact Or.inl rfl
      · split
        · rename_i r hm
          exact Or.inr (Or.inl ⟨o, r.1, r.2, ho, hc, hm, rfl⟩)
        · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- Finishing an item keeps the game well formed. -/
theorem finishItem_wf {s : GameState} (hwf : s.WF) (item : ObjId) : (finishItem s item).1.WF := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, -, hm, h⟩ | ⟨o, s2, -, -, -, hr, h⟩
  · rw [h]; exact hwf
  · rw [h]; exact moveObj_wf hwf hm
  · rw [h]; exact removeObj_wf hwf hr

/-- Finishing an item keeps the physical cards. -/
theorem finishItem_physIds {s : GameState} (hwf : s.WF) (item : ObjId) :
    (finishItem s item).1.physIds.Perm s.physIds := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, -, hm, h⟩ | ⟨o, s2, ho, -, hk, hr, h⟩
  · rw [h]
  · rw [h]; exact moveObj_physIds hwf hm
  · rw [h]; exact removeObj_physIds hwf hr ho hk

/-- Finishing an item keeps `OwnerOk`. -/
theorem finishItem_ownerOk {s : GameState} (hwf : s.WF) (hown : s.OwnerOk) (item : ObjId) :
    (finishItem s item).1.OwnerOk := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, -, hm, h⟩ | ⟨o, s2, -, -, -, hr, h⟩
  · rw [h]; exact hown
  · rw [h]; exact moveObj_ownerOk hwf hown hm
  · rw [h]; exact removeObj_ownerOk hwf hown hr

/-- Finishing an item changes only the zones, the objects and the counters. -/
theorem finishItem_sameMeta (s : GameState) (item : ObjId) : SameMeta s (finishItem s item).1 := by
  rcases finishItem_cases s item with
      h | ⟨o, s2, id', -, -, hm, h⟩ | ⟨o, s2, -, -, -, hr, h⟩
  · rw [h]; exact SameMeta.refl s
  · rw [h]; exact (moveObj_spec hm).choose_spec.choose_spec.other
  · rw [h]; exact removeObj_sameMeta hr

/-- Resolving the Chain puts some frames on top of the stack below. -/
theorem resolveFrames_eq (s : GameState) (rest : List Frame) :
    ∃ pre, resolveFrames s rest = pre ++ rest ∧ ∀ g ∈ pre, g.isPlay = true := by
  unfold resolveFrames
  split
  · split
    · rename_i _ item _ _ _ _ o _ _ _
      split
      · let steps := (o.spellPick.executions o.targets).map fun (pick, targets) =>
          Frame.run o.controller item { hiddenPlayLocation := o.hiddenAt, shownOff := o.shownOff }
            (.cons (.resolveSpellExecution pick targets) .nil)
        refine ⟨steps ++ [.finishSpell item], by simp [steps, List.append_assoc], ?_⟩
        intro g hg
        rcases List.mem_append.mp hg with hm | hf
        · obtain ⟨⟨pick, targets⟩, _, rfl⟩ := List.mem_map.mp hm
          rfl
        · obtain rfl := List.mem_singleton.mp hf
          rfl
      · exact ⟨[.run _ _ _ _, .finishSpell _], rfl, by simp [Frame.isPlay]⟩
    · unfold itemFrames
      split
      · exact ⟨[.run _ _ _ _, .finishSpell _], rfl, by simp [Frame.isPlay]⟩
      · exact ⟨[.finishSpell _], rfl, by simp [Frame.isPlay]⟩
    · exact ⟨[.finishSpell _], rfl, by simp [Frame.isPlay]⟩
  · exact ⟨[], rfl, by simp⟩

end Riftbound

end
