module

public import Riftbound.Rules.Play
public import Riftbound.Rules.Remove
public import Riftbound.Rules.Owner
public import Riftbound.Rules.Actions.BurnOut

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

end GameState

/-- Put each object of the list through `g`, one after the other: the last state, and all the
events. -/
def applyEach (g : GameState → ObjId → GameState × List Event) :
    GameState → List ObjId → GameState × List Event
  | s, [] => (s, [])
  | s, id :: ids =>
    let r := g s id
    let r2 := applyEach g r.1 ids
    (r2.1, r.2 ++ r2.2)

/-- Putting each object through changes that are safe is a safe change. -/
theorem applyEach_safe {g : GameState → ObjId → GameState × List Event}
    (hg : ∀ s id, Safe s (g s id).1) : ∀ (ids : List ObjId) (s : GameState),
      Safe s (applyEach g s ids).1
  | [], s => Safe.refl s
  | id :: ids, s => (hg s id).trans (applyEach_safe hg ids (g s id).1)

/-- Send an object to the zone `k` of its owner. Nothing happens if it is not on a zone. -/
def sendObj (k : ZoneKind) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    match moveObj s id (.player o.owner k) with
    | some r => (r.1, [Event.moved id r.2 (.player o.owner k)])
    | none => (s, [])
  | none => (s, [])

/-- Sending an object to a zone is a safe change. -/
theorem sendObj_safe (k : ZoneKind) (s : GameState) (id : ObjId) :
    Safe s (sendObj k s id).1 := by
  unfold sendObj
  split
  · split
    · rename_i r hm
      exact Safe.moveObj hm
    · exact Safe.refl s
  · exact Safe.refl s

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

/-- Make an effect true for the rest of the turn, for the player. -/
def GameState.addTurnFx (s : GameState) (p : PlayerId) (e : TurnEffect) : GameState :=
  { s with turnFx := s.turnFx ++
      [{ who := p, turn := s.turn, stamp := s.nextTimestamp, kind := e }] }

/-- The same, about an object. -/
def GameState.addTurnFxOn (s : GameState) (p : PlayerId) (id : ObjId) (e : TurnEffect) :
    GameState :=
  { s with turnFx := s.turnFx ++
      [{ who := p, turn := s.turn, stamp := s.nextTimestamp, kind := e, target := some id }] }

/-- A lasting effect about an object is a safe change. -/
theorem addTurnFxOn_safe (s : GameState) (p : PlayerId) (id : ObjId) (e : TurnEffect) :
    Safe s (s.addTurnFxOn p id e) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- A lasting effect of the turn is a safe change: it is not part of what a safe change keeps. -/
theorem addTurnFx_safe (s : GameState) (p : PlayerId) (e : TurnEffect) :
    Safe s (s.addTurnFx p e) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

/-- Do the change if the condition holds. -/
def noteIf (b : Bool) (f : GameState → GameState) (s : GameState) : GameState :=
  if b then f s else s

/-- A change that is safe, done if a condition holds, is a safe change. -/
theorem noteIf_safe (b : Bool) (f : GameState → GameState) (hf : ∀ t, Safe t (f t))
    (s : GameState) : Safe s (noteIf b f s) := by
  unfold noteIf
  split
  · exact hf s
  · exact Safe.refl s

/-- The notes of the death of a unit: that it died, and whether it was buffed or stunned as it died
(the notes are about the dead card, which is the object it has become). -/
def noteDeath (s : GameState) (o : Object) (isUnit : Bool) (marked : Bool)
    (moved : Option ObjId) : GameState :=
  let s1 := noteIf (isUnit && moved.isSome) (fun t => t.addTurnFx o.controller .unitDied) s
  match moved with
  | some n =>
    let s2 := noteIf (isUnit && o.buffed)
      (fun t => t.addTurnFxOn o.controller n .buffedUnitDied) s1
    let s3 := noteIf (isUnit && o.stunned)
      (fun t => t.addTurnFxOn o.controller n .stunnedUnitDied) s2
    noteIf (isUnit && marked) (fun t => t.addTurnFxOn o.controller n .recallDied) s3
  | none => s1

/-- Noting a death is a safe change. -/
theorem noteDeath_safe (s : GameState) (o : Object) (isUnit marked : Bool) (moved : Option ObjId) :
    Safe s (noteDeath s o isUnit marked moved) := by
  unfold noteDeath
  have h1 := noteIf_safe (isUnit && moved.isSome) (fun t => t.addTurnFx o.controller .unitDied)
    (fun t => addTurnFx_safe t _ _) s
  cases moved with
  | none => exact h1
  | some n =>
    refine h1.trans ?_
    exact ((noteIf_safe _ _ (fun t => addTurnFxOn_safe t _ _ _) _).trans
      (noteIf_safe _ _ (fun t => addTurnFxOn_safe t _ _ _) _)).trans
      (noteIf_safe _ _ (fun t => addTurnFxOn_safe t _ _ _) _)

/-- Kill an object: it goes to its owner's Trash. -/
def killObj (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := sendObj .trash s id
  match s.obj? id with
  | some o =>
    -- the death of a unit is noted for the turn (its controller, as it died)
    (noteDeath r.1 o ((s.cardDef? id).any (·.hasType .unit))
        (s.turnFx.any (fun f => f.kind == .recallOnDeath && f.target == some id &&
          f.turn == s.turn))
        (r.2.findSome? (fun e => match e with | .moved _ n _ => some n | _ => none)),
      r.2 ++ r.2.filterMap (fun e => match e with
      | .moved _ n _ => some (Event.died n o.controller)
      | _ => none))
  | none => r

/-- Killing an object is a safe change. -/
theorem killObj_safe (s : GameState) (id : ObjId) : Safe s (killObj s id).1 := by
  unfold killObj
  split
  · exact (sendObj_safe .trash s id).trans (noteDeath_safe _ _ _ _ _)
  · exact sendObj_safe .trash s id

/-- Deal `n` damage to an object (CR 142). An object whose damage reaches its Might is killed by
the next Cleanup (CR 323.4), not here. -/
def dealObj (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some _ =>
    -- an object whose passive ability says it takes no damage takes none
    if (s.activeMods id).contains .noDamage then (s, [])
    else
      let s1 := s.modObj id (fun o => { o with damage := o.damage + n })
      -- a unit that takes damage while an effect of the turn says so is killed
      if decide (0 < n) && (s.cardDef? id).any (·.hasType .unit) && s.killOnHit id then
        let k := killObj s1 id
        (k.1, Event.damaged id n :: k.2)
      else (s1, [Event.damaged id n])
  | none => (s, [])

/-- Dealing damage is a safe change. -/
theorem dealObj_safe (n : Nat) (s : GameState) (id : ObjId) : Safe s (dealObj n s id).1 := by
  unfold dealObj
  split
  · split
    · exact Safe.refl s
    · dsimp only
      have h1 : Safe s (s.modObj id (fun o => { o with damage := o.damage + n })) :=
        Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
      split
      · exact h1.trans (killObj_safe _ id)
      · exact h1
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

/-- Make an object ready or exhausted (CR 415, 416). -/
def setExhausted (b : Bool) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    -- only an object that was exhausted is readied, and only a ready one is exhausted (CR 416)
    (s.modObj id (fun o => { o with exhausted := b }),
      if b then [Event.exhausted id] else if o.exhausted then [Event.readied id] else [])
  | none => (s, [])

/-- Readying or exhausting is a safe change. -/
theorem setExhausted_safe (b : Bool) (s : GameState) (id : ObjId) :
    Safe s (setExhausted b s id).1 := by
  unfold setExhausted
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

/-- A spell or an ability cannot ready the Units and Gear of the opponents of a player who has a
passive ability that says so. -/
def readyBlocked (s : GameState) (id : ObjId) : Bool :=
  (s.obj? id).any (fun o => s.oppHas o.controller .noReadyOfOpps) &&
    (s.cardDef? id).any (fun d => d.hasType .unit || d.hasType .gear)

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

/-- The card is a token the rules print: its number has a T, as SFD-T03 (Gold) has. -/
def CardDef.isTokenCard (c : CardDef) : Bool := (c.id.code.splitOn "-T").length > 1

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

/-- Stun an object: it deals no combat damage this turn (CR 424). -/
def stunObj (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with stunned := true }), [Event.stunned id])

/-- Stunning is a safe change. -/
theorem stunObj_safe (s : GameState) (id : ObjId) : Safe s (stunObj s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

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
    else { o with buffed := false }), [])

/-- Spending a buff is a safe change. -/
theorem unbuffObj_safe (s : GameState) (id : ObjId) : Safe s (unbuffObj s id).1 :=
  Safe.modObj s id (fun _ => by split <;> rfl) (fun _ => by split <;> rfl)

/-- The player gains XP (CR 728): it goes to their Legend. -/
def gainXPOf (n : Nat) (s : GameState) (p : PlayerId) : GameState :=
  match s.zone (.player p .legendZone) with
  | l :: _ => s.modObj l (fun o => { o with xp := o.xp + n })
  | [] => s

/-- Gaining XP is a safe change. -/
theorem gainXPOf_safe (n : Nat) (s : GameState) (p : PlayerId) : Safe s (gainXPOf n s p) := by
  unfold gainXPOf
  split
  · exact Safe.modObj s _ (fun _ => rfl) (fun _ => rfl)
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
def enterBase (d : CardDef) (mk : PlayMark) (rdy : Bool) (s : GameState) (id : ObjId) :
    GameState :=
  let s2 := s.modObj id (fun o => (Object.freshPlay mk o).cleared)
  if d.hasType .unit && !rdy then (setExhausted true s2 id).1 else s2

/-- Entering the Base is a safe change. -/
theorem enterBase_safe (d : CardDef) (mk : PlayMark) (rdy : Bool) (s : GameState) (id : ObjId) :
    Safe s (enterBase d mk rdy s id) := by
  have h1 : Safe s (s.modObj id (fun o => (Object.freshPlay mk o).cleared)) :=
    Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  unfold enterBase
  split
  · exact h1.trans (setExhausted_safe true _ _)
  · exact h1

/-- Play a card without paying its cost (CR 349): a Unit or a Gear goes to the Base of the player,
exhausted if it is a Unit that does not enter ready, and the play is noted, so that what waits for a
card to be played fires. A card that is in the Base already is played again where it is. -/
def playFree (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.cardDef? id with
  | some d =>
    -- only a Unit or a Gear enters the Base; a Spell would need the Chain
    if !(d.hasType .unit || d.hasType .gear) then (s, []) else
    match moveObj s id (.player p .base) with
    | some r =>
      (enterBase d (s.playMark p id ⟨0, []⟩) (s.readyNow p id d) r.1 r.2,
        [Event.moved id r.2 (.player p .base), Event.played p r.2])
    | none =>
      if s.locate id = some (.player p .base) then
        (enterBase d (s.playMark p id ⟨0, []⟩) (s.readyNow p id d) s id, [Event.played p id])
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
        exact (Safe.moveObj hr).trans (enterBase_safe _ _ _ _ _)
      · split
        · exact enterBase_safe _ _ _ _ _
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

/-- Counter a spell: it leaves the Chain for the Trash of its owner without resolving (CR 359.3.d).
Nothing happens to what is not a spell on the Chain. -/
def counterObj (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some o =>
    if id ∈ s.zone .chain then
      match o.kind with
      | .chainAbility .. => (s, [])
      | _ =>
        match moveObj s id (.player o.owner .trash) with
        | some r => (r.1, [Event.moved id r.2 (.player o.owner .trash)])
        | none => (s, [])
    else (s, [])
  | none => (s, [])

/-- Countering a spell is a safe change. -/
theorem counterObj_safe (s : GameState) (id : ObjId) : Safe s (counterObj s id).1 := by
  unfold counterObj
  split
  · split
    · split
      · exact Safe.refl s
      · split
        · rename_i r hr
          exact Safe.moveObj hr
        · exact Safe.refl s
    · exact Safe.refl s
  · exact Safe.refl s

/-- Discard a card: it goes to the Trash of its owner, and the discard is noted (CR 423). -/
def discardObj (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := sendObj .trash s id
  match s.obj? id with
  | some o =>
    ((if r.2.isEmpty then r.1 else r.1.addTurnFx o.owner .cardDiscarded),
      r.2 ++ r.2.filterMap (fun e =>
      match e with
      | .moved _ n _ => some (Event.discarded o.owner n true)
      | _ => none))
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

/-- Replacing a Rune Pool is a safe change. -/
theorem setPool_safe (s : GameState) (p : PlayerId) (pool : RunePool) : Safe s (s.setPool p pool) :=
  ⟨fun hwf => hwf.congr rfl rfl rfl rfl, fun _ => List.Perm.refl _,
    fun _ hown => hown.congr rfl rfl, rfl⟩

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

/-- Channel `n` Runes ready, and `extra` more that enter exhausted (CR 431). -/
def channelEx (p : PlayerId) (n extra : Nat) (s : GameState) : GameState × List Event :=
  let r1 := channel p n s
  let r2 := channel p extra r1.1
  (exhaustAll (movedNew r2.2) r2.1, r1.2 ++ r2.2)

/-- Channeling some Runes exhausted is a safe change. -/
theorem channelEx_safe (p : PlayerId) (n extra : Nat) (s : GameState) :
    Safe s (channelEx p n extra s).1 :=
  ((channel_safe p n s).trans (channel_safe p extra _)).trans (exhaustAll_safe _ _)

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

/-- Move an object to its controller's Base: a move, not a Recall (CR 144, 456). Its damage and
status stay. -/
def sendHome (s : GameState) (u : ObjId) : GameState × List Event :=
  match s.obj? u with
  | some o =>
    match moveObj s u (.player o.controller .base) with
    | some r => (r.1.modObj r.2 (fun o => { o with loc := none }), [])
    | none => (s, [])
  | none => (s, [])

/-- Moving to the Base is a safe change. -/
theorem sendHome_safe (s : GameState) (u : ObjId) : Safe s (sendHome s u).1 := by
  unfold sendHome
  split
  · split
    · rename_i r hm
      exact (Safe.moveObj hm).trans (Safe.modObj _ _ (fun _ => rfl) (fun _ => rfl))
    · exact Safe.refl s
  · exact Safe.refl s

/-- The Battlefield is Contested by the player if the player does not control it (CR 190.3). A
Battlefield that is Contested already keeps the player who made it so: the rule that a Unit cannot
be moved to a Battlefield with a Combat in progress (CR 449.2.a) is not written yet. -/
def contestFor (p : PlayerId) (bf : ObjId) (s : GameState) : GameState :=
  if (s.obj? bf).bind (·.control) = some p ∨ ((s.obj? bf).bind (·.contested)).isSome then s
  else s.modObj bf (fun b => { b with contested := some p })

/-- Contesting is a safe change. -/
theorem contestFor_safe (p : PlayerId) (bf : ObjId) (s : GameState) :
    Safe s (contestFor p bf s) := by
  unfold contestFor
  split
  · exact Safe.refl s
  · exact Safe.modObj s bf (fun _ => rfl) (fun _ => rfl)

/-- Move a Unit to a Battlefield by an effect (CR 447): it is not exhausted, and it stays where it
is if it is there already. Its controller contests the Battlefield. -/
def sendToBf (bf : ObjId) (s : GameState) (u : ObjId) : GameState × List Event :=
  match s.obj? u with
  | some o =>
    if o.loc = some bf then (s, [])
    else if u ∈ s.zone .battlefieldZone then
      (contestFor o.controller bf
        (s.modObj u (fun x => ({ x with loc := some bf } : Object).countMove s.turn x.loc)),
        [Event.standardMoved u (some bf)])
    else
      match moveObj s u .battlefieldZone with
      | some r =>
        (contestFor o.controller bf
          (r.1.modObj r.2 (fun x => ({ x with loc := some bf } : Object).countMove s.turn x.loc)),
          [Event.standardMoved r.2 (some bf)])
      | none => (s, [])
  | none => (s, [])

/-- Moving to a Battlefield is a safe change. -/
theorem sendToBf_safe (bf : ObjId) (s : GameState) (u : ObjId) : Safe s (sendToBf bf s u).1 := by
  unfold sendToBf
  split
  · split
    · exact Safe.refl s
    · split
      · rename_i o ho hl hz
        have h1 : Safe s
            (s.modObj u
              (fun x => ({ x with loc := some bf } : Object).countMove s.turn x.loc)) :=
          Safe.modObj s u (fun _ => rfl) (fun _ => rfl)
        exact h1.trans (contestFor_safe _ _ _)
      · split
        · rename_i o ho hl hz r hm
          have h1 : Safe r.1
              (r.1.modObj r.2
                (fun x => ({ x with loc := some bf } : Object).countMove s.turn x.loc)) :=
            Safe.modObj r.1 r.2 (fun _ => rfl) (fun _ => rfl)
          exact ((Safe.moveObj hm).trans h1).trans (contestFor_safe _ _ _)
        · exact Safe.refl s
  · exact Safe.refl s

/-- Move a Unit to the Base of its controller by an effect, unless the Battlefield it is at
forbids it (CR 447). -/
def moveHome (s : GameState) (u : ObjId) : GameState × List Event :=
  if ((s.obj? u).bind (·.loc)).any (fun bf => (s.activeMods bf).contains .noMoveToBase) then
    (s, [])
  else sendHome s u

/-- Moving home is a safe change. -/
theorem moveHome_safe (s : GameState) (u : ObjId) : Safe s (moveHome s u).1 := by
  unfold moveHome
  split
  · exact Safe.refl s
  · exact sendHome_safe s u

/-- Move a Unit to a place by an effect: a Battlefield (`some`) or its controller's Base. -/
def sendToLoc (loc : Option ObjId) (s : GameState) (u : ObjId) : GameState × List Event :=
  match loc with
  | some bf => sendToBf bf s u
  | none => sendHome s u

/-- Moving to a place is a safe change. -/
theorem sendToLoc_safe (loc : Option ObjId) (s : GameState) (u : ObjId) :
    Safe s (sendToLoc loc s u).1 := by
  cases loc with
  | none => exact sendHome_safe s u
  | some bf => exact sendToBf_safe bf s u

/-- Two Units swap places by an effect: each goes to where the other is. Nothing happens if they are
at the same place, or if a Battlefield that a Unit would leave for the Base forbids it. -/
def swapPlaces (s : GameState) (x y : ObjId) : GameState × List Event :=
  let lx := (s.obj? x).bind (·.loc)
  let ly := (s.obj? y).bind (·.loc)
  let forbids (l : Option ObjId) : Bool :=
    l.any (fun bf => (s.activeMods bf).contains .noMoveToBase)
  if lx == ly || (lx.isNone && forbids ly) || (ly.isNone && forbids lx) then (s, [])
  else
    let r1 := sendToLoc ly s x
    let r2 := sendToLoc lx r1.1 y
    (r2.1, r1.2 ++ r2.2)

/-- Swapping places is a safe change. -/
theorem swapPlaces_safe (s : GameState) (x y : ObjId) : Safe s (swapPlaces s x y).1 := by
  unfold swapPlaces
  dsimp only
  split
  · exact Safe.refl s
  · exact (sendToLoc_safe _ s x).trans (sendToLoc_safe _ _ y)

/-- Play a card without paying, to a Battlefield: it is played, and moved there (CR 447). -/
def playFreeAt (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := playFree p s id
  match movedNew r.2 with
  | n :: _ =>
    -- the card is played there: it does not move, so nothing that waits for a move fires, and
    -- no move is counted
    (((sendToBf bf r.1 n).1.modObj n (fun x => { x with moves := 0, movesTurn := none })), r.2)
  | [] => r

/-- Playing a card to a Battlefield is a safe change. -/
theorem playFreeAt_safe (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) :
    Safe s (playFreeAt p bf s id).1 := by
  unfold playFreeAt
  cases hm : movedNew (playFree p s id).2 with
  | nil => simpa [hm] using playFree_safe p s id
  | cons n _ =>
    simp only [hm]
    exact ((playFree_safe p s id).trans (sendToBf_safe bf _ _)).trans
      (Safe.modObj _ n (fun _ => rfl) (fun _ => rfl))


/-- Play a card without paying, to a Battlefield: to its Base, if the opponents of the player play
Units only to their Base (Mageseeker Warden). -/
def playToOrBase (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  if s.oppHas p .oppsPlayToBaseOnly then playFree p s id else playFreeAt p bf s id

/-- Playing a card to a Battlefield or to the Base is a safe change. -/
theorem playToOrBase_safe (p : PlayerId) (bf : ObjId) (s : GameState) (id : ObjId) :
    Safe s (playToOrBase p bf s id).1 := by
  unfold playToOrBase
  split
  · exact playFree_safe p s id
  · exact playFreeAt_safe p bf s id
/-- A player takes control of an object (CR 740). -/
def setController (p : PlayerId) (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with controller := p }), [])

/-- Taking control is a safe change. -/
theorem setController_safe (p : PlayerId) (s : GameState) (id : ObjId) :
    Safe s (setController p s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- Recall a Unit: it goes to its controller's Base, and is exhausted if the effect says so. It is
not a move, so no ability of a move fires (CR 456). -/
def recallFx (ex : Bool) (s : GameState) (u : ObjId) : GameState × List Event :=
  let r := sendHome s u
  if ex then ((setExhausted true r.1 u).1, r.2 ++ (setExhausted true r.1 u).2) else r

/-- Recalling is a safe change. -/
theorem recallFx_safe (ex : Bool) (s : GameState) (u : ObjId) : Safe s (recallFx ex s u).1 := by
  unfold recallFx
  cases ex
  · exact sendHome_safe s u
  · exact (sendHome_safe s u).trans (setExhausted_safe true _ u)

/-- Attach an Equipment to a Unit (CR 137, 825). -/
def attachTo (u : ObjId) (s : GameState) (g : ObjId) : GameState × List Event :=
  (s.modObj g (fun o => { o with attached := some u }), [])

/-- Attaching is a safe change. -/
theorem attachTo_safe (u : ObjId) (s : GameState) (g : ObjId) : Safe s (attachTo u s g).1 :=
  Safe.modObj s g (fun _ => rfl) (fun _ => rfl)

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

/-- Play tokens: `n` of them on the player's Base or here, if the token is in the game's cards
(CR 183). `none` if it cannot be done yet. -/
def applyCreate (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (name : String)
    (n : Amount) (place : Place) (ready : Bool) : Option (GameState × List Event) :=
  (n.evalS s p src env).bind (fun k =>
    match s.tokenCard name with
    | none => none
    | some c =>
      match place with
      | .atBase => some (createN c.id p none ready k s, [])
      | .here => (s.hereOf src).map (fun bf => (createN c.id p (some bf) ready k s, []))
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
        exact createN_safe _ _ _ _ _ _
      | here =>
        cases hh : s.hereOf src with
        | none => simp [hh] at h
        | some bf =>
          simp only [hh, Option.map_some, Option.some.injEq] at h
          rw [← h]
          exact createN_safe _ _ _ _ _ _
      | anywhere => simp at h
      | atBattlefield => simp at h
      | inHand => simp at h
      | inTrash => simp at h
      | inMainDeck => simp at h
      | inRuneDeck => simp at h
      | inHidden => simp at h
      | inCombat => simp at h
      | onChain => simp at h

/-- Do a game action that changes objects: the new state and the events. `none` if the action is
not understood yet, or what it names cannot be found. -/
def applyPrim (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) :
    Prim → Option (GameState × List Event)
  | .deal sel n =>
    if s.damageOff then some (s, []) else
    (n.evalS s p src env).bind (fun k => onSelected s p src env sel
      (fun t id => dealObj (if 0 < k then k + s.bonusOn p src id else k) t id))
  | .heal sel n => (n.evalS s p src env).bind (fun k => onSelected s p src env sel (healOne k))
  | .kill sel =>
    -- a unit killed by a spell is noted, for what waits for that (Immortal Phoenix)
    (onSelected s p src env sel killObj).map (fun r =>
      (r.1, r.2 ++ (if (s.cardDef? src).any (·.hasType .spell) &&
          r.2.any (fun e => match e with
            | .died n _ => (r.1.cardDef? n).any (·.hasType .unit)
            | _ => false)
        then [Event.killedBySpell p] else [])))
  | .ready sel => onSelected s p src env sel readyEffect
  | .exhaust sel => onSelected s p src env sel (setExhausted true)
  | .banish sel => onSelected s p src env sel (sendObj .banishment)
  | .returnToHand sel => onSelected s p src env sel (sendObj .hand)
  | .create name n place ready => applyCreate s p src env name n place ready
  | .attach gears to => applyAttach s p src env gears to
  | .move sel .base => onSelected s p src env sel moveHome
  | .move sel (.at_ dsel) =>
    -- the place of the first object the destination names: a Battlefield, or where a Unit is
    match dsel.eval s p src env with
    | some (d :: _) =>
      -- a Battlefield, or the Battlefield a Unit is at; a Unit at a Base names no place yet
      match (if (s.cardDef? d).any (·.hasType .battlefield) then some d
          else (s.obj? d).bind (·.loc)) with
      | some bf => onSelected s p src env sel (sendToLoc (some bf))
      | none => none
    | _ => none
  | .swapPlaces a b =>
    match a.eval s p src env, b.eval s p src env with
    | some (x :: _), some (y :: _) => some (swapPlaces s x y)
    | _, _ => none
  | .stun sel => onSelected s p src env sel stunObj
  | .buff sel => onSelected s p src env sel buffObj
  | .gainXP ps n =>
    (ps.resolve s p).bind (fun l => (n.evalS s p src env).map (fun k => (gainXPAll k s l, [])))
  | .channel ps n extra =>
    (ps.resolve s p).bind (fun l =>
      (n.evalS s p src env).bind (fun k =>
        (extra.evalS s p src env).map (fun x => channelAll k x s l)))
  | .recycle sel =>
    -- recycling a card that is a card (not a Rune), even in its deck, is noted
    (sel.eval s p src env).map (fun ids =>
      let r := applyEach recycleOne s ids
      (r.1, r.2 ++ (if ids.any (fun id => (s.obj? id).isSome && recycleKind s id == .mainDeck)
        then [Event.recycled p] else [])))
  -- revealing shows information: nothing changes, but the object is chosen
  | .reveal _ => some (s, [])
  | .spendBuff sel => onSelected s p src env sel unbuffObj
  | .play sel => onSelected s p src env sel (playFree p)
  | .playTo sel bfs =>
    match bfs.eval s p src env with
    | some (b :: _) => onSelected s p src env sel (playToOrBase p b)
    | _ => none
  | .bin sel => onSelected s p src env sel (fun t id => sendObj .trash t id)
  | .discardCard sel => onSelected s p src env sel discardObj
  | .counter sel => onSelected s p src env sel counterObj
  | .hideAt sel bfs =>
    match bfs.eval s p src env with
    | some (b :: _) => onSelected s p src env sel (hideObj b)
    | _ => none
  | .recycleTop ps =>
    (ps.resolve s p).map (fun l => (recycleTopAll s l,
      l.filterMap (fun q =>
        if (s.zone (.player q .mainDeck)).isEmpty then none else some (Event.recycled q))))
  | .takeControl sel => onSelected s p src env sel (setController p)
  | .recall sel ex => onSelected s p src env sel (recallFx ex)
  | .win ps =>
    -- winning is reaching the Victory Score: the Cleanup that follows declares the winner
    (ps.resolve s p).map (fun l =>
      (gainPointsAll s.victoryScore s l, []))
  | .score ps n =>
    (ps.resolve s p).bind (fun l => (n.evalS s p src env).map (fun k =>
      (gainPointsAll k s l, if k = 0 then [] else l.map (fun q => Event.pointsGained q k))))
  | .turnEffect e =>
    some (s.addTurnFx p e, if e == .hiddenPlayed then [Event.hiddenPlayed p] else [])
  | .playFirst fs => some (playFirstOf fs p src env s)
  | .markOn sel e => onSelected s p src env sel (fun t id => (t.addTurnFxOn p id e, []))
  | .returnChampion => some (returnChampion p s)
  | .activateConquer sel =>
    onSelected s p src env sel (fun t id => (t, [Event.conquerActivated id]))
  | .pay c =>
    match s.payNow p src c with
    | some pool => some (s.setPool p pool, [])
    | none => some (s, [])
  | .addEnergy ps n none =>
    (ps.resolve s p).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addEnergy k) s l, [])))
  | .addPower ps n (some d) none =>
    (ps.resolve s p).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addPower d k) s l, [])))
  | .addPower ps n none none =>
    (ps.resolve s p).bind (fun l => (n.evalS s p src env).map (fun k =>
      (poolsMap (fun pool => pool.addAny k) s l, [])))
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
        exact onSelected_safe (fun t id => dealObj_safe _ t id) h
  | heal sel n =>
    simp only [applyPrim] at h
    cases hn : n.evalS s p src env with
    | none => simp [hn] at h
    | some k =>
      simp only [hn, Option.bind_some] at h
      exact onSelected_safe (healOne_safe k) h
  | kill sel =>
    simp only [applyPrim] at h
    cases hs : onSelected s p src env sel killObj with
    | none => simp [hs] at h
    | some r0 =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      have h0 := onSelected_safe killObj_safe hs
      rw [← h]
      exact h0
  | ready sel => exact onSelected_safe readyEffect_safe h
  | exhaust sel => exact onSelected_safe (setExhausted_safe true) h
  | banish sel => exact onSelected_safe (sendObj_safe .banishment) h
  | returnToHand sel => exact onSelected_safe (sendObj_safe .hand) h
  | create name n place ready => exact applyCreate_safe h
  | attach gears to => exact applyAttach_safe h
  | move sel dest =>
    cases dest with
    | base => exact onSelected_safe moveHome_safe h
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
          · exact onSelected_safe (sendToLoc_safe _) h
          · simp at h
  | stun sel => exact onSelected_safe stunObj_safe h
  | buff sel => exact onSelected_safe buffObj_safe h
  | gainXP ps n =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h]
        exact gainXPAll_safe k l s
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
  | spendBuff sel => exact onSelected_safe unbuffObj_safe h
  | play sel => exact onSelected_safe (playFree_safe p) h
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
  | bin sel => exact onSelected_safe (fun t id => sendObj_safe .trash t id) h
  | discardCard sel => exact onSelected_safe discardObj_safe h
  | counter sel => exact onSelected_safe counterObj_safe h
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
    cases hl : ps.resolve s p with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact recycleTopAll_safe l s
  | takeControl sel => exact onSelected_safe (setController_safe p) h
  | «recall» sel ex => exact onSelected_safe (recallFx_safe ex) h
  | win ps =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact gainPointsAll_safe _ l s
  | score ps n =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p with
    | none => simp [hl] at h
    | some l =>
      cases hn : n.evalS s p src env with
      | none => simp [hl, hn] at h
      | some k =>
        simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h]
        exact gainPointsAll_safe k l s
  | channel ps n extra =>
    simp only [applyPrim] at h
    cases hl : ps.resolve s p with
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
            exact swapPlaces_safe s x y
  | activateConquer sel =>
    simp only [applyPrim] at h
    exact onSelected_safe (fun t id => Safe.refl t) h
  | markOn sel e =>
    simp only [applyPrim] at h
    exact onSelected_safe (fun t id => addTurnFxOn_safe t p id e) h
  | turnEffect e =>
    simp only [applyPrim, Option.some.injEq] at h
    rw [← h]
    exact addTurnFx_safe s p e
  | addEnergy ps n only =>
    cases only with
    | some a => simp [applyPrim] at h
    | none =>
      simp only [applyPrim] at h
      cases hl : ps.resolve s p with
      | none => simp [hl] at h
      | some l =>
        cases hn : n.evalS s p src env with
        | none => simp [hl, hn] at h
        | some k =>
          simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
          rw [← h]
          exact poolsMap_safe _ l s
  | addPower ps n d only =>
    cases d with
    | none =>
      cases only with
      | some a => simp [applyPrim] at h
      | none =>
        simp only [applyPrim] at h
        cases hl : ps.resolve s p with
        | none => simp [hl] at h
        | some l =>
          cases hn : n.evalS s p src env with
          | none => simp [hl, hn] at h
          | some k =>
            simp only [hl, hn, Option.bind_some, Option.map_some, Option.some.injEq] at h
            rw [← h]
            exact poolsMap_safe _ l s
    | some dom =>
      cases only with
      | some a => simp [applyPrim] at h
      | none =>
        simp only [applyPrim] at h
        cases hl : ps.resolve s p with
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
    cases hp : s.payNow p src c with
    | none => simp only [hp, Option.some.injEq] at h; subst h; exact Safe.refl s
    | some pool =>
      simp only [hp, Option.some.injEq] at h
      subst h
      exact setPool_safe s p pool
  | _ => simp [applyPrim] at h

/-- When a lasting effect ends, if the model has a way to end it. -/
def Duration.endPoint? : Duration → Option EndPoint
  | .thisTurn => some .turn
  | .permanent => some .never
  | _ => none

/-- Add a lasting change of Might to an object (CR 475-478). -/
def addMightMod (m : MightMod) (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with mightMods := o.mightMods ++ [m] }), [])

/-- Adding a change of Might is a safe change. -/
theorem addMightMod_safe (m : MightMod) (s : GameState) (id : ObjId) :
    Safe s (addMightMod m s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- Give an object a keyword for a while (CR 479.3). -/
def addTempKw (k : KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    GameState × List Event :=
  (s.modObj id (fun o => { o with tempKws := o.tempKws ++ [(k, ends)] }), [])

/-- Giving a keyword for a while is a safe change. -/
theorem addTempKw_safe (k : KeywordInst) (ends : EndPoint) (s : GameState) (id : ObjId) :
    Safe s (addTempKw k ends s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

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

/-- Change the Might of objects for a while: `sign` is 1 for more, -1 for less. -/
def applyGrant (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (m : StaticMod) (d : Duration) : Option (GameState × List Event) :=
  let go (a : Amount) (sign : Int) : Option (GameState × List Event) :=
    d.endPoint?.bind (fun ends => (a.evalS s p src env).bind (fun k =>
      onSelected s p src env sel (addMightMod ⟨sign * (k : Int), ends⟩)))
  match m with
  | .mightPlus .it a => go a 1
  | .mightMinus .it a => go a (-1)
  | .mightMinusMin .it a fl =>
    d.endPoint?.bind (fun ends => (a.evalS s p src env).bind (fun k =>
      onSelected s p src env sel (addMightFloor k fl ends)))
  | .keyword .it k => d.endPoint?.bind (fun ends => onSelected s p src env sel (addTempKw k ends))
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
        exact onSelected_safe (addMightMod_safe _) h
  · cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      cases hk : (‹Amount›).evalS s p src env with
      | none => simp [hd, hk] at h
      | some k =>
        simp only [hd, hk, Option.bind_some] at h
        exact onSelected_safe (addMightFloor_safe _ _ _) h
  · cases hd : d.endPoint? with
    | none => simp [hd] at h
    | some ends =>
      simp only [hd, Option.bind_some] at h
      exact onSelected_safe (addTempKw_safe _ _) h
  · simp at h

/-- The selector of a primitive that is chosen while the effect resolves, if it has one. -/
def Prim.pickSel? : Prim → Option Selector
  | .deal s _ => some s
  | .heal s _ => some s
  | .kill s => some s
  | .ready s => some s
  | .exhaust s => some s
  | .banish s => some s
  | .returnToHand s => some s
  | .stun s => some s
  | .buff s => some s
  | .recycle s => some s
  | .spendBuff s => some s
  | .bin s => some s
  | .discardCard s => some s
  | .play s => some s
  | .markOn s _ => some s
  | .playTo s _ => some s
  | .reveal s => some s
  | .move s d =>
    match s, d with
    | .pick .one _ _ _, _ => some s
    | _, .at_ (.pick .one side place fs) => some (.pick .one side place fs)
    | _, _ => none
  | _ => none

/-- The primitive with its selector replaced. -/
def Prim.withSel (p : Prim) (sel : Selector) : Prim :=
  match p with
  | .deal _ n => .deal sel n
  | .heal _ n => .heal sel n
  | .kill _ => .kill sel
  | .ready _ => .ready sel
  | .exhaust _ => .exhaust sel
  | .banish _ => .banish sel
  | .returnToHand _ => .returnToHand sel
  | .stun _ => .stun sel
  | .buff _ => .buff sel
  | .recycle _ => .recycle sel
  | .spendBuff _ => .spendBuff sel
  | .bin _ => .bin sel
  | .discardCard _ => .discardCard sel
  | .play _ => .play sel
  | .markOn _ e => .markOn sel e
  | .playTo _ bf => .playTo sel bf
  | .reveal _ => .reveal sel
  | .move s d =>
    match s, d with
    | .pick .one _ _ _, _ => .move sel d
    | _, .at_ (.pick .one _ _ _) => .move s (.at_ sel)
    | _, _ => .move s d
  | q => q

/-- The effect names one object to choose while it resolves ("kill a gear", "stun a unit"): the
selector that does it. -/
def Effect.pickSel? : Effect → Option Selector
  | .prim p =>
    match p.pickSel? with
    | some (.pick .one side place fs) => some (.pick .one side place fs)
    | _ => none
  | .grant (.pick .one side place fs) _ _ => some (.pick .one side place fs)
  | _ => none

/-- The effect with the chosen object, named by `pickVar`, in place of the selector. -/
def Effect.withPick : Effect → Effect
  | .prim p => .prim (p.withSel (.var pickVar))
  | .grant (.pick .one _ _ _) m d => .grant (.var pickVar) m d
  | e => e

/-- Do the first effect of `e :: es`, but not a choice: the new state, the frames that replace the
`run` frame, and the events. -/
def runEffect1 (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : GameState × List Frame × List Event :=
  let skip : GameState × List Frame × List Event := (s, [.run p src env es], [Event.skipped src])
  match e with
  | .nop => (s, [.run p src env es], [])
  | .seq l => (s, [.run p src env (l.append es)], [])
  | .bind v a e' =>
    match a.evalS s p src env with
    | some k => (s, [.run p src (env.bind v (.int k)) (.cons e' .nil), .run p src env es], [])
    | none => skip
  | .ifThen c t e' =>
    match c.eval s p src env with
    | some b => (s, [.run p src env (.cons (if b then t else e') es)], [])
    | none => skip
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
    match who.resolve s p with
    | some ps => (s, ps.map (fun q => Frame.run q src env (.cons body .nil)) ++
        [.run p src env es], [])
    | none => skip
  | .may e' => (s, [.mayDo p src env e' es], [])
  | .eitherOf .nil => skip
  | .eitherOf (.cons a rest) =>
    -- the player chooses between the first effect ("yes") and the others ("no"), and so on
    match rest with
    | .nil => (s, [.run p src env (.cons a es)], [])
    | .cons b .nil => (s, [.eitherDo p src env a b es], [])
    | r => (s, [.eitherDo p src env a (.eitherOf r) es], [])
  | .prim (.draw sel n) =>
    match sel.resolve s p, n.evalS s p src env with
    | some ps, some k => (s, ps.map (fun q => Frame.draw q k) ++ [.run p src env es], [])
    | _, _ => skip
  | .prim (.discard sel n) =>
    match sel.resolve s p, n.evalS s p src env with
    | some ps, some k => (s, ps.map (fun q => Frame.discard q k) ++ [.run p src env es], [])
    | _, _ => skip
  | .prim pr =>
    match applyPrim s p src env pr with
    | some r => (r.1, [.run p src env es], r.2)
    | none => skip
  | .grant sel m d =>
    match applyGrant s p src env sel m d with
    | some r => (r.1, [.run p src env es], r.2)
    | none => skip
  | _ => skip

/-- Doing an effect, but not a choice, is a safe change of the state. -/
theorem runEffect1_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : Safe s (runEffect1 s p src env e es).1 := by
  unfold runEffect1
  split <;> (try split) <;> first
    | exact Safe.refl s
    | (rename_i r hr; exact applyPrim_safe hr)
    | (rename_i r hr; exact applyGrant_safe hr)

/-- Do the first effect of `e :: es`: the new state, the frames that replace the `run` frame, and
the events. An instruction that cannot be done is skipped (design.md §7.1). An effect that names an
object to choose while it resolves ("kill a gear") asks the player when there is more than one to
choose from, and goes on with the only one when there is one (CR 355). -/
def runEffect (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : GameState × List Frame × List Event :=
  match e.pickSel? with
  | some (.pick _ side place fs) =>
    match s.pickCandidates p src env side place fs with
    | some [o] => (s, [.run p src (env.bind pickVar (.obj o)) (.cons e.withPick es)], [])
    | some (o :: o2 :: more) => (s, [.pickDo p src env o (o2 :: more) e.withPick es], [])
    | _ => (s, [.run p src env es], [Event.skipped src])
  | _ => runEffect1 s p src env e es

/-- Doing an effect is a safe change of the state. -/
theorem runEffect_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : Safe s (runEffect s p src env e es).1 := by
  unfold runEffect
  split
  · split
    · exact Safe.refl s
    · exact Safe.refl s
    · exact Safe.refl s
  · exact runEffect1_safe s p src env e es

/-- What an ability on the Chain does: the effect of the ability the card has at that place
(CR 361). Nothing if the card or the ability is not there. -/
def abilityBody (s : GameState) (card : CardId) (idx : Nat) : EffectList :=
  match s.cards.find? card with
  | some d =>
    match d.allAbilities[idx]? with
    | some (.activated _ _ b _) => .cons b.body .nil
    | some (.triggered _ b _) => .cons b.body .nil
    | _ => .nil
  | none => .nil

/-- The frames that resolve an item of the Chain that is not a card: an ability runs its effect for
its controller, with the objects chosen as the slots, and then it leaves the Chain (CR 340). -/
def itemFrames (s : GameState) (item : ObjId) (o : Object) (rest : List Frame) : List Frame :=
  match o.kind with
  | .chainAbility card idx src =>
    .run o.controller src { slots := o.targets.map Value.obj } (abilityBody s card idx) ::
      .finishSpell item :: rest
  | _ => .finishSpell item :: rest

/-- The frames that resolve the item on top of the Chain (CR 340): run its effect, then it leaves
the Chain (a Spell goes to the Trash, an ability ceases to exist). Nothing to resolve when the
Chain is empty. -/
def resolveFrames (s : GameState) (rest : List Frame) : List Frame :=
  match s.zone .chain with
  | item :: _ =>
    match s.obj? item, s.cardDef? item with
    | some o, some d =>
      .run o.controller item { slots := o.targets.map Value.obj }
        (match d.spellEffect with
          | some e => if o.paid then .cons e.body (.cons e.body .nil) else .cons e.body .nil
          | none => .nil) :: .finishSpell item :: rest
    | some o, none => itemFrames s item o rest
    | none, _ => .finishSpell item :: rest
  | [] => rest

/-- An item has resolved: a Spell goes from the Chain to its owner's Trash (CR 359.3.d), an ability
ceases to exist. Nothing happens if it is no longer on the Chain. -/
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
        match moveObj s item (.player o.owner .trash) with
        | some r => (r.1, [Event.moved item r.2 (.player o.owner .trash)])
        | none => (s, [])
    else (s, [])
  | none => (s, [])

/-- The frames to put under the Cleanup after an item has resolved: while the Chain still holds
items, the turn player gets priority again (CR 340). -/
def afterItem (s : GameState) : List Frame :=
  if (s.zone .chain).isEmpty then [] else [.chainPass (s.active.getD ⟨0⟩) 0]

/-- The frames under the Cleanup after an item has resolved are a `chainPass`. -/
theorem afterItem_mem {s : GameState} {f : Frame} (h : f ∈ afterItem s) :
    ∃ p, f = .chainPass p 0 := by
  unfold afterItem at h
  split at h
  · simp at h
  · simp only [List.mem_singleton] at h
    exact ⟨_, h⟩

/-- Finishing an item either changes nothing, or moves a Spell from the Chain to its owner's Trash,
or removes an ability. -/
theorem finishItem_cases (s : GameState) (item : ObjId) :
    (finishItem s item).1 = s ∨
      (∃ o s2 id', s.obj? item = some o ∧ item ∈ s.zone .chain ∧
        moveObj s item (.player o.owner .trash) = some (s2, id') ∧
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
    · exact ⟨[.run _ _ _ _, .finishSpell _], rfl, by simp [Frame.isPlay]⟩
    · unfold itemFrames
      split
      · exact ⟨[.run _ _ _ _, .finishSpell _], rfl, by simp [Frame.isPlay]⟩
      · exact ⟨[.finishSpell _], rfl, by simp [Frame.isPlay]⟩
    · exact ⟨[.finishSpell _], rfl, by simp [Frame.isPlay]⟩
  · exact ⟨[], rfl, by simp⟩

end Riftbound

end
