module

public import Riftbound.Rules.Play
public import Riftbound.Rules.Remove

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

/-- Kill an object: it goes to its owner's Trash. -/
def killObj (s : GameState) (id : ObjId) : GameState × List Event :=
  let r := sendObj .trash s id
  match s.obj? id with
  | some o =>
    (r.1, r.2 ++ r.2.filterMap (fun e => match e with
      | .moved _ n _ => some (Event.died n o.controller)
      | _ => none))
  | none => r

/-- Killing an object is a safe change. -/
theorem killObj_safe (s : GameState) (id : ObjId) : Safe s (killObj s id).1 := by
  unfold killObj
  split
  · exact sendObj_safe .trash s id
  · exact sendObj_safe .trash s id

/-- Deal `n` damage to an object (CR 142). An object whose damage reaches its Might is killed by
the next Cleanup (CR 323.4), not here. -/
def dealObj (n : Nat) (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | some _ => (s.modObj id (fun o => { o with damage := o.damage + n }), [Event.damaged id n])
  | none => (s, [])

/-- Dealing damage is a safe change. -/
theorem dealObj_safe (n : Nat) (s : GameState) (id : ObjId) : Safe s (dealObj n s id).1 := by
  unfold dealObj
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
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
  | some _ =>
    (s.modObj id (fun o => { o with exhausted := b }),
      [if b then Event.exhausted id else Event.readied id])
  | none => (s, [])

/-- Readying or exhausting is a safe change. -/
theorem setExhausted_safe (b : Bool) (s : GameState) (id : ObjId) :
    Safe s (setExhausted b s id).1 := by
  unfold setExhausted
  split
  · exact Safe.modObj s id (fun _ => rfl) (fun _ => rfl)
  · exact Safe.refl s

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
  (s.modObj id (fun o => { o with stunned := true }), [])

/-- Stunning is a safe change. -/
theorem stunObj_safe (s : GameState) (id : ObjId) : Safe s (stunObj s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

/-- Buff an object: it gets a +1 Might buff if it has none (CR 701). -/
def buffObj (s : GameState) (id : ObjId) : GameState × List Event :=
  (s.modObj id (fun o => { o with buffed := true }), [])

/-- Buffing is a safe change. -/
theorem buffObj_safe (s : GameState) (id : ObjId) : Safe s (buffObj s id).1 :=
  Safe.modObj s id (fun _ => rfl) (fun _ => rfl)

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
      | inCombat => simp at h

/-- Do a game action that changes objects: the new state and the events. `none` if the action is
not understood yet, or what it names cannot be found. -/
def applyPrim (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) :
    Prim → Option (GameState × List Event)
  | .deal sel n => (n.evalS s p src env).bind (fun k => onSelected s p src env sel (dealObj k))
  | .heal sel n => (n.evalS s p src env).bind (fun k => onSelected s p src env sel (healOne k))
  | .kill sel => onSelected s p src env sel killObj
  | .ready sel => onSelected s p src env sel (setExhausted false)
  | .exhaust sel => onSelected s p src env sel (setExhausted true)
  | .banish sel => onSelected s p src env sel (sendObj .banishment)
  | .returnToHand sel => onSelected s p src env sel (sendObj .hand)
  | .create name n place ready => applyCreate s p src env name n place ready
  | .attach gears to => applyAttach s p src env gears to
  | .move sel .base => onSelected s p src env sel sendHome
  | .stun sel => onSelected s p src env sel stunObj
  | .buff sel => onSelected s p src env sel buffObj
  | .gainXP ps n =>
    (ps.resolve s p).bind (fun l => (n.evalS s p src env).map (fun k => (gainXPAll k s l, [])))
  | .channel ps n extra =>
    (ps.resolve s p).bind (fun l =>
      (n.evalS s p src env).bind (fun k =>
        (extra.evalS s p src env).map (fun x => channelAll k x s l)))
  | _ => none

/-- An action that is done is a safe change. -/
theorem applyPrim_safe {s : GameState} {p : PlayerId} {src : ObjId} {env : Env} {pr : Prim}
    {r : GameState × List Event} (h : applyPrim s p src env pr = some r) : Safe s r.1 := by
  cases pr with
  | deal sel n =>
    simp only [applyPrim] at h
    cases hn : n.evalS s p src env with
    | none => simp [hn] at h
    | some k =>
      simp only [hn, Option.bind_some] at h
      exact onSelected_safe (dealObj_safe k) h
  | heal sel n =>
    simp only [applyPrim] at h
    cases hn : n.evalS s p src env with
    | none => simp [hn] at h
    | some k =>
      simp only [hn, Option.bind_some] at h
      exact onSelected_safe (healOne_safe k) h
  | kill sel => exact onSelected_safe killObj_safe h
  | ready sel => exact onSelected_safe (setExhausted_safe false) h
  | exhaust sel => exact onSelected_safe (setExhausted_safe true) h
  | banish sel => exact onSelected_safe (sendObj_safe .banishment) h
  | returnToHand sel => exact onSelected_safe (sendObj_safe .hand) h
  | create name n place ready => exact applyCreate_safe h
  | attach gears to => exact applyAttach_safe h
  | move sel dest =>
    cases dest with
    | base => exact onSelected_safe sendHome_safe h
    | at_ t => simp [applyPrim] at h
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

/-- Change the Might of objects for a while: `sign` is 1 for more, -1 for less. -/
def applyGrant (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (sel : Selector)
    (m : StaticMod) (d : Duration) : Option (GameState × List Event) :=
  let go (a : Amount) (sign : Int) : Option (GameState × List Event) :=
    d.endPoint?.bind (fun ends => (a.evalS s p src env).bind (fun k =>
      onSelected s p src env sel (addMightMod ⟨sign * (k : Int), ends⟩)))
  match m with
  | .mightPlus .it a => go a 1
  | .mightMinus .it a => go a (-1)
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
  · simp at h

/-- Do the first effect of `e :: es`: the new state, the frames that replace the `run` frame, and
the events. An instruction that cannot be done is skipped (design.md §7.1). -/
def runEffect (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
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

/-- Doing an effect is a safe change of the state. -/
theorem runEffect_safe (s : GameState) (p : PlayerId) (src : ObjId) (env : Env) (e : Effect)
    (es : EffectList) : Safe s (runEffect s p src env e es).1 := by
  unfold runEffect
  split <;> (try split) <;> first
    | exact Safe.refl s
    | (rename_i r hr; exact applyPrim_safe hr)
    | (rename_i r hr; exact applyGrant_safe hr)

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
