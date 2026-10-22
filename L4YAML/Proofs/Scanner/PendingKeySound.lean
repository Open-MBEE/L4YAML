/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Scanner.PendingKeysStable
public import L4YAML.Proofs.Scanner.IndentStackMono
public import L4YAML.Proofs.Scanner.ExplicitKeyCoupling
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey
public import L4YAML.Proofs.Scanner.ScannerEkStackPreservation
public import L4YAML.Proofs.Scanner.IndentStackCover
@[expose] public section Blanket

/-!
# The explicit-key register IS the innermost pending key (DOCS item 338)

Item 335 gave every indentation level one `pendingKeys` slot and made the
scanner re-read the register (`explicitKeyLine`, `explicitKeyCol`) off the
innermost marked level whenever a level closes.  Item 337's hook closes a level
on a dedenting `-`.  What those two items bought is a TOKEN-LEVEL invariant,
stated and carried here:

* `SlotsOk` — `pendingKeys` is in lockstep with `indents`, and a marked slot sits
  on a level of column `≥ 0` (never the sentinel);
* `RegOk`   — outside flow, the register pair equals `PendingKeys.innermost`;
* `BaseOk`  — inside flow, the pair saved at the OUTERMOST flow open (the bottom
  of `explicitKeyStack`) equals the innermost pending key, which no flow token
  moves (the block writers are `!inFlow`-guarded) — lane (d) of item 334;
* `StackOk` — `explicitKeyStack` has one saved pair per open flow level.

It is a property of the state BETWEEN tokens, not of every intermediate state:
`unwindIndents` pops marked levels before the stale-key hook re-reads the
register (which is why it is not a `ScannerSurfCorr` field — item 338 priced
and refuted that shape), and the one hook exemption that survives a pop is the
`?` the next `scanKey` overwrites.  So `preprocess_sound` concludes `RegOk` only
for `c ≠ '?'`, and `scanKey_sound` needs no `RegOk` premise.

§1 the `PendingKeys` array lemmas (`innermost` read structurally).  §2 the
predicate and its transport.  §3 the writers.  §4 the preprocess and the four
dispatchers.  §5 the step and the seed.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.PendingKeySound

open L4YAML.Scanner
open L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML.Proofs.IndentStackBase (SentinelBase)
open L4YAML.Proofs.IndentStackMono (Mono)

/-! ## §1  `PendingKeys.innermost`, read structurally -/

/-- `innermost` read top-down, structurally. -/
def go (cols : Array Int) (pks : Array (Option Nat)) : Nat → Option Nat × Int
  | 0 => (none, -1)
  | i + 1 =>
    match pks[i]?.getD none with
    | some l => (some l, cols[i]?.getD (-1))
    | none => go cols pks i

lemma findSomeRev_range_eq (cols : Array Int) (pks : Array (Option Nat)) (n : Nat) :
    ((Array.range n).findSomeRev? (fun i =>
        (pks[i]?.getD none).map fun l => (l, cols[i]?.getD (-1)))) =
      match go cols pks n with
      | (some l, c) => some (l, c)
      | (none, _) => none := by
  induction n with
  | zero =>
    first
      | rfl
      | (rw [show Array.range 0 = #[] from Array.eq_empty_of_size_eq_zero (by simp)]; rfl)
      | simp [go]
  | succ n ih =>
    rw [Array.range_succ, Array.append_singleton, Array.findSomeRev?_push]
    simp only [go]
    cases h : pks[n]?.getD none with
    | none => simp; split <;> simp_all
    | some l => simp

lemma go_none_snd (cols : Array Int) (pks : Array (Option Nat)) (n : Nat)
    (h : (go cols pks n).1 = none) : (go cols pks n).2 = -1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [go] at h ⊢
    split at h
    · simp at h
    · exact ih h

lemma innermost_eq_go (cols : Array Int) (pks : Array (Option Nat)) :
    PendingKeys.innermost cols pks = go cols pks pks.size := by
  unfold PendingKeys.innermost
  rw [findSomeRev_range_eq]
  cases h : go cols pks pks.size with
  | mk l c =>
    cases l with
    | some l => simp
    | none =>
      have := go_none_snd cols pks pks.size (by rw [h])
      rw [h] at this; simp at this; simp [this]

/-- `go` only reads slots below `n`; pushing a slot above them changes nothing. -/
lemma go_push (cols : Array Int) (pks : Array (Option Nat)) (c : Int) (x : Option Nat)
    (hsz : cols.size = pks.size) (n : Nat) (hn : n ≤ pks.size) :
    go (cols.push c) (pks.push x) n = go cols pks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [go]
    rw [Array.getElem?_push_lt (by omega), Array.getElem?_push_lt (by omega),
        Array.getElem?_eq_getElem (by omega : n < pks.size),
        Array.getElem?_eq_getElem (by omega : n < cols.size), ih (by omega)]

lemma innermost_push_none (cols : Array Int) (pks : Array (Option Nat)) (c : Int)
    (hsz : cols.size = pks.size) :
    PendingKeys.innermost (cols.push c) (pks.push none) = PendingKeys.innermost cols pks := by
  rw [innermost_eq_go, innermost_eq_go, Array.size_push]
  simp only [go, Array.getElem?_push_size, Option.getD_some]
  exact go_push cols pks c none hsz pks.size (Nat.le_refl _)

lemma go_pop (cols : Array Int) (pks : Array (Option Nat)) (n : Nat) (hn : n < pks.size)
    (hc : n < cols.size) :
    go cols.pop pks.pop n = go cols pks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [go]
    rw [Array.getElem?_pop, Array.getElem?_pop]
    simp only [show n < pks.size - 1 from by omega, show n < cols.size - 1 from by omega, ↓reduceIte]
    rw [ih (by omega) (by omega)]

/-- Popping an UNMARKED top slot keeps the innermost pending key. -/
lemma innermost_pop_of_top_none (cols : Array Int) (pks : Array (Option Nat))
    (hsz : cols.size = pks.size) (hpos : 0 < pks.size)
    (htop : pks[pks.size - 1]? = some none) :
    PendingKeys.innermost cols.pop pks.pop = PendingKeys.innermost cols pks := by
  rw [innermost_eq_go, innermost_eq_go, Array.size_pop]
  obtain ⟨k, hk⟩ : ∃ k, pks.size = k + 1 := ⟨pks.size - 1, by omega⟩
  rw [hk]; simp only [Nat.add_sub_cancel, go]
  rw [hk] at htop; simp only [Nat.add_sub_cancel] at htop
  rw [htop]; simp only [Option.getD_some]
  exact go_pop cols pks k (by omega) (by omega)

/-- Marking the top slot makes it the innermost pending key. -/
lemma innermost_set_top (cols : Array Int) (pks : Array (Option Nat)) (l : Nat)
    (_hsz : cols.size = pks.size) (hpos : 0 < pks.size) :
    PendingKeys.innermost cols (pks.set! (pks.size - 1) (some l)) =
      (some l, cols[pks.size - 1]?.getD (-1)) := by
  rw [innermost_eq_go, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  obtain ⟨k, hk⟩ : ∃ k, pks.size = k + 1 := ⟨pks.size - 1, by omega⟩
  rw [hk]; simp only [Nat.add_sub_cancel, go]
  rw [Array.getElem?_setIfInBounds_self]
  simp only [show k < pks.size from by omega, ↓reduceIte, Option.getD_some]

/-- A marked slot's witness: the innermost pair names a slot of `pks`. -/
lemma go_some_mem (cols : Array Int) (pks : Array (Option Nat)) (n : Nat) (l : Nat) (c : Int)
    (h : go cols pks n = (some l, c)) :
    ∃ i, i < n ∧ pks[i]? = some (some l) ∧ cols[i]?.getD (-1) = c := by
  induction n with
  | zero => simp [go] at h
  | succ n ih =>
    simp only [go] at h
    cases hp : pks[n]?.getD none with
    | some l' =>
      rw [hp] at h; simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨n, Nat.lt_succ_self _, ?_, rfl⟩
      cases hq : pks[n]? with
      | none => simp [hq] at hp
      | some v => simp [hq] at hp; simp [hp]
    | none =>
      rw [hp] at h
      obtain ⟨i, hi, h1, h2⟩ := ih h
      exact ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩

lemma innermost_some_mem (cols : Array Int) (pks : Array (Option Nat)) (l : Nat) (c : Int)
    (h : PendingKeys.innermost cols pks = (some l, c)) :
    ∃ i, i < pks.size ∧ pks[i]? = some (some l) ∧ cols[i]?.getD (-1) = c := by
  rw [innermost_eq_go] at h; exact go_some_mem cols pks _ l c h

/-- `closeAt` only erases slots. -/
lemma closeAt_getElem? (cols : Array Int) (pks : Array (Option Nat)) (col : Int) (i : Nat) :
    (PendingKeys.closeAt cols pks col)[i]? =
      if i < pks.size then some (if cols[i]? == some col then none else pks[i]?.getD none)
      else none := by
  unfold PendingKeys.closeAt
  rw [Array.getElem?_map, Array.getElem?_range]
  split <;> rfl

lemma closeAt_size (cols : Array Int) (pks : Array (Option Nat)) (col : Int) :
    (PendingKeys.closeAt cols pks col).size = pks.size := by
  simp [PendingKeys.closeAt]

lemma closeAt_marked (cols : Array Int) (pks : Array (Option Nat)) (col : Int) (i l : Nat)
    (h : (PendingKeys.closeAt cols pks col)[i]? = some (some l)) :
    pks[i]? = some (some l) ∧ cols[i]? ≠ some col := by
  rw [closeAt_getElem?] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · cases h
    · rename_i hne
      refine ⟨?_, fun hc => hne (by simp [hc])⟩
      cases hq : pks[i]? with
      | none => simp [hq] at h
      | some v => simp [hq] at h; simp [h]
  · cases h


/-! ## §2  The predicate -/

/-- `pendingKeys` is in lockstep with `indents`, and every marked slot sits on a
    level of column `≥ 0`. -/
def SlotsOk (s : ScannerState) : Prop :=
  s.pendingKeys.size = s.indents.size ∧
  ∀ (i l : Nat), s.pendingKeys[i]? = some (some l) →
    ∃ c, s.indentColumns[i]? = some c ∧ 0 ≤ c

/-- Outside flow the register IS the innermost pending key. -/
def RegOk (s : ScannerState) : Prop :=
  s.flowLevel = 0 → (s.explicitKeyLine, s.explicitKeyCol) = s.innermostPendingKey

/-- Inside flow the pair saved at the outermost open is the innermost pending key. -/
def BaseOk (s : ScannerState) : Prop :=
  0 < s.flowLevel → s.explicitKeyStack[0]? = some s.innermostPendingKey

/-- One saved pair per open flow level. -/
def StackOk (s : ScannerState) : Prop := s.explicitKeyStack.size = s.flowLevel

structure Sound (s : ScannerState) : Prop where
  slots : SlotsOk s
  reg : RegOk s
  base : BaseOk s
  stack : StackOk s

lemma indentColumns_size (s : ScannerState) : s.indentColumns.size = s.indents.size := by
  simp [ScannerState.indentColumns]

lemma innermostPendingKey_eq (s : ScannerState) :
    s.innermostPendingKey = PendingKeys.innermost s.indentColumns s.pendingKeys := rfl

/-- Transport along a step that moves none of the six fields the predicate reads. -/
lemma Sound.of_eq {s s' : ScannerState} (h : Sound s)
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents)
    (hfl : s'.flowLevel = s.flowLevel)
    (hekl : s'.explicitKeyLine = s.explicitKeyLine) (hekc : s'.explicitKeyCol = s.explicitKeyCol)
    (hst : s'.explicitKeyStack = s.explicitKeyStack) : Sound s' := by
  have hcols : s'.indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : s'.innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0; rw [hekl, hekc, hinn]; exact h.reg (hfl ▸ h0)
  · intro h0; rw [hst, hinn]; exact h.base (hfl ▸ h0)
  · show s'.explicitKeyStack.size = s'.flowLevel
    rw [hst, hfl]; exact h.stack

/-! ## §3  The writers -/

lemma indentColumns_push (s : ScannerState) (e : IndentEntry) :
    ({ s with indents := s.indents.push e } : ScannerState).indentColumns =
      s.indentColumns.push e.column := by
  simp [ScannerState.indentColumns]

lemma SlotsOk.push_none {s s' : ScannerState} (h : SlotsOk s) (e : IndentEntry)
    (hind : s'.indents = s.indents.push e) (hpk : s'.pendingKeys = s.pendingKeys.push none) :
    SlotsOk s' := by
  have hsz := h.1
  have hcols : s'.indentColumns = s.indentColumns.push e.column := by
    simp [ScannerState.indentColumns, hind]
  refine ⟨by simp [hind, hpk, hsz], ?_⟩
  intro i l hi
  rw [hpk] at hi
  rw [hcols]
  by_cases hlt : i < s.pendingKeys.size
  · rw [Array.getElem?_push_lt hlt] at hi
    obtain ⟨c, hc, hc0⟩ := h.2 i l (by rw [Array.getElem?_eq_getElem hlt]; exact hi)
    refine ⟨c, ?_, hc0⟩
    rw [Array.getElem?_push_lt (by rw [indentColumns_size]; omega)]
    rw [Array.getElem?_eq_getElem (by rw [indentColumns_size]; omega)] at hc
    exact hc
  · by_cases heq : i = s.pendingKeys.size
    · subst heq; rw [Array.getElem?_push_size] at hi; cases hi
    · rw [Array.getElem?_eq_none (by simp [Array.size_push]; omega)] at hi; cases hi

lemma pushMappingIndent_slots (s : ScannerState) (col : Int) (h : SlotsOk s) :
    SlotsOk (pushMappingIndent s col) := by
  unfold pushMappingIndent
  split
  · exact h.push_none { column := col, isSequence := false } (by simp [ScannerState.emit])
      (by simp [ScannerState.emit])
  · exact h

/-- A level pushed with an empty slot: nothing the predicate reads moves except
    the lockstep sizes. -/
lemma Sound.push_none {s s' : ScannerState} (h : Sound s) (e : IndentEntry)
    (hind : s'.indents = s.indents.push e) (hpk : s'.pendingKeys = s.pendingKeys.push none)
    (hfl : s'.flowLevel = s.flowLevel)
    (hekl : s'.explicitKeyLine = s.explicitKeyLine) (hekc : s'.explicitKeyCol = s.explicitKeyCol)
    (hst : s'.explicitKeyStack = s.explicitKeyStack) : Sound s' := by
  have hsz := h.slots.1
  have hcols : s'.indentColumns = s.indentColumns.push e.column := by
    simp [ScannerState.indentColumns, hind]
  have hinn : s'.innermostPendingKey = s.innermostPendingKey := by
    rw [innermostPendingKey_eq, innermostPendingKey_eq, hcols, hpk]
    exact innermost_push_none _ _ _ (by rw [indentColumns_size]; exact hsz.symm)
  refine ⟨⟨by simp [hind, hpk, hsz], ?_⟩, ?_, ?_, ?_⟩
  · intro i l hi
    rw [hpk] at hi
    rw [hcols]
    by_cases hlt : i < s.pendingKeys.size
    · rw [Array.getElem?_push_lt hlt] at hi
      obtain ⟨c, hc, hc0⟩ := h.slots.2 i l (by rw [Array.getElem?_eq_getElem hlt]; exact hi)
      refine ⟨c, ?_, hc0⟩
      rw [Array.getElem?_push_lt (by rw [indentColumns_size]; omega)]
      rw [Array.getElem?_eq_getElem (by rw [indentColumns_size]; omega)] at hc
      exact hc
    · by_cases heq : i = s.pendingKeys.size
      · subst heq; rw [Array.getElem?_push_size] at hi; cases hi
      · rw [Array.getElem?_eq_none (by simp [Array.size_push]; omega)] at hi; cases hi
  · intro h0; rw [hekl, hekc, hinn]; exact h.reg (hfl ▸ h0)
  · intro h0; rw [hst, hinn]; exact h.base (hfl ▸ h0)
  · show s'.explicitKeyStack.size = s'.flowLevel
    rw [hst, hfl]; exact h.stack

lemma pushSequenceIndent_sound (s : ScannerState) (col : Int) (h : Sound s) :
    Sound (pushSequenceIndent s col) := by
  unfold pushSequenceIndent
  split
  · exact h.push_none _ rfl rfl rfl rfl rfl rfl
  · exact h

lemma pushMappingIndent_sound (s : ScannerState) (col : Int) (h : Sound s) :
    Sound (pushMappingIndent s col) := by
  unfold pushMappingIndent
  split
  · exact h.push_none _ rfl rfl rfl rfl rfl rfl
  · exact h

/-- `closeAt` only erases slots, so `SlotsOk` survives it. -/
lemma clearPendingKeyAt_slots {s : ScannerState} (h : SlotsOk s) (col : Int) :
    SlotsOk (s.clearPendingKeyAt col) := by
  refine ⟨by simp [ScannerState.clearPendingKeyAt, closeAt_size, h.1], ?_⟩
  intro i l hi
  simp only [ScannerState.clearPendingKeyAt] at hi
  exact h.2 i l (closeAt_marked _ _ _ _ _ hi).1

/-- Re-reading the register off the stack restores `RegOk` by construction, and
    touches nothing else. -/
lemma readPendingKey_sound {s : ScannerState} (hs : SlotsOk s) (hb : BaseOk s) (hst : StackOk s) :
    Sound s.readPendingKey :=
  ⟨hs, fun _ => rfl, hb, hst⟩

/-- The hook is the identity in flow, and in block context `BaseOk` is vacuous,
    so the re-read restores `RegOk` and costs nothing else. -/
lemma closeStaleExplicitKey_sound {s : ScannerState} (h : Sound s) :
    Sound (closeStaleExplicitKey s) := by
  by_cases hf : s.inFlow = true
  · rw [closeStaleExplicitKey_of_inFlow s hf]; exact h
  · have h0 : s.flowLevel = 0 := by
      simp [ScannerState.inFlow] at hf; omega
    rcases closeStaleExplicitKey_cases s with heq | heq <;> rw [heq]
    · exact h
    · exact readPendingKey_sound (clearPendingKeyAt_slots h.slots _)
        (fun hpos => absurd hpos (by simp [ScannerState.clearPendingKeyAt, h0])) h.stack

lemma indentColumns_getElem? (s : ScannerState) (i : Nat) :
    s.indentColumns[i]? = s.indents[i]?.map (·.column) := by
  simp [ScannerState.indentColumns]

/-- One pop of the loop: both arrays lose their top, nothing else the predicate
    reads moves. -/
lemma unwindPop_fields (s : ScannerState) :
    let s' : ScannerState :=
      { (s.emit .blockEnd) with indents := (s.emit .blockEnd).indents.pop,
                                pendingKeys := (s.emit .blockEnd).pendingKeys.pop }
    s'.indents = s.indents.pop ∧ s'.pendingKeys = s.pendingKeys.pop ∧
    s'.flowLevel = s.flowLevel ∧ s'.explicitKeyLine = s.explicitKeyLine ∧
    s'.explicitKeyCol = s.explicitKeyCol ∧ s'.explicitKeyStack = s.explicitKeyStack := by
  simp [ScannerState.emit, ScannerState.emitAt]

lemma SlotsOk.pop {s s' : ScannerState} (h : SlotsOk s)
    (hind : s'.indents = s.indents.pop) (hpk : s'.pendingKeys = s.pendingKeys.pop) :
    SlotsOk s' := by
  refine ⟨by simp [hind, hpk, Array.size_pop, h.1], ?_⟩
  intro i l hi
  rw [hpk, Array.getElem?_pop] at hi
  split at hi
  · obtain ⟨c, hc, hc0⟩ := h.2 i l hi
    refine ⟨c, ?_, hc0⟩
    rw [indentColumns_getElem?, hind, Array.getElem?_pop]
    rw [indentColumns_getElem?] at hc
    have hsz := h.1
    rw [if_pos (by omega)]; exact hc
  · cases hi

lemma unwindIndentsLoop_slots (s : ScannerState) (col : Int) (fuel : Nat) (h : SlotsOk s) :
    SlotsOk (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => simpa [unwindIndentsLoop] using h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · obtain ⟨h1, h2, -⟩ := unwindPop_fields s
      exact ih _ (h.pop h1 h2)
    · exact h

/-- The top slot is empty when the top column exceeds every marked column. -/
lemma top_slot_none {s : ScannerState} (hs : SlotsOk s) (col : Int)
    (hmarked : ∀ (i l : Nat), s.pendingKeys[i]? = some (some l) →
      s.indentColumns[i]?.getD (-1) ≤ col)
    (hgt : s.currentIndent > col) (hpos : 0 < s.indents.size) :
    s.pendingKeys[s.pendingKeys.size - 1]? = some none := by
  have hsz := hs.1
  have hlt : s.pendingKeys.size - 1 < s.pendingKeys.size := by omega
  rw [Array.getElem?_eq_getElem hlt]
  cases hv : s.pendingKeys[s.pendingKeys.size - 1] with
  | none => rfl
  | some l =>
    exfalso
    have hm := hmarked _ l (by rw [Array.getElem?_eq_getElem hlt, hv])
    rw [indentColumns_getElem?] at hm
    unfold ScannerState.currentIndent at hgt
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)] at hgt
    rw [hsz, Array.getElem?_eq_getElem (by omega)] at hm
    simp at hm hgt
    omega

/-- Popping levels whose columns exceed every marked slot's column keeps the
    innermost pending key (the popped slots are empty). -/
lemma innermost_of_pop {s s' : ScannerState} (hs : SlotsOk s)
    (hind : s'.indents = s.indents.pop) (hpk : s'.pendingKeys = s.pendingKeys.pop)
    (hpos : 0 < s.pendingKeys.size)
    (htop : s.pendingKeys[s.pendingKeys.size - 1]? = some none) :
    s'.innermostPendingKey = s.innermostPendingKey := by
  rw [innermostPendingKey_eq, innermostPendingKey_eq]
  have hcols : s'.indentColumns = s.indentColumns.pop := by
    simp [ScannerState.indentColumns, hind, Array.map_pop]
  rw [hcols, hpk]
  exact innermost_pop_of_top_none _ _ (by rw [indentColumns_size]; exact hs.1.symm) hpos htop

lemma unwindIndentsLoop_innermost (s : ScannerState) (col : Int) (fuel : Nat)
    (hs : SlotsOk s)
    (hmarked : ∀ (i l : Nat), s.pendingKeys[i]? = some (some l) →
      s.indentColumns[i]?.getD (-1) ≤ col) :
    (unwindIndentsLoop s col fuel).innermostPendingKey = s.innermostPendingKey := by
  induction fuel generalizing s with
  | zero => simp [unwindIndentsLoop]
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · rename_i hguard
      obtain ⟨h1, h2, -⟩ := unwindPop_fields s
      have hsz := hs.1
      have hg : s.currentIndent > col ∧ s.indents.size > 1 := by simpa using hguard
      refine (ih _ (hs.pop h1 h2) ?_).trans
        (innermost_of_pop hs h1 h2 (by omega) (top_slot_none hs col hmarked hg.1 (by omega)))
      intro i l hi
      rw [h2, Array.getElem?_pop] at hi
      split at hi
      · have := hmarked i l hi
        rw [indentColumns_getElem?, h1, Array.getElem?_pop, if_pos (by omega)]
        rw [indentColumns_getElem?] at this; exact this
      · cases hi
    · rfl

/-- The `?`'s own write, block context: the level under it is marked. -/
lemma scanKey_pendingKeys {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanKey s = .ok s') :
    s'.pendingKeys = (pushMappingIndent s (s.col : Int)).pendingKeys.set!
      ((pushMappingIndent s (s.col : Int)).indents.size - 1) (some s.line) := by
  unfold scanKey at hok
  simp only [bind, Except.bind, h_noflow, Bool.not_false, ite_true] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals simp [h_noflow, advance_preserves_pendingKeys, emit_pendingKeys,
    L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit]

lemma inFlow_false_iff (s : ScannerState) : s.inFlow = false ↔ s.flowLevel = 0 := by
  simp [ScannerState.inFlow]

lemma scanKey_sound {s s' : ScannerState} (hok : scanKey s = .ok s')
    (hs : SlotsOk s) (hb : BaseOk s) (hst : StackOk s) (hbase : SentinelBase s)
    (hcol : s.inFlow = false → s.currentIndent ≤ (s.col : Int)) : Sound s' := by
  have hfl : s'.flowLevel = s.flowLevel :=
    L4YAML.Proofs.ScannerCorrectness.scanKey_preserves_flowLevel s s' hok
  have hstk : s'.explicitKeyStack = s.explicitKeyStack :=
    L4YAML.Proofs.ScannerEkStack.scanKey_preserves_explicitKeyStack s s' hok
  obtain ⟨hekl, hekc⟩ := L4YAML.Proofs.ExplicitKeyCoupling.scanKey_ok_explicitKey hok
  by_cases hf : s.inFlow = true
  · -- flow: slots and stack untouched, the register conjunct is vacuous
    have hpk := scanKey_pendingKeys_of_inFlow hf hok
    have hind := L4YAML.Proofs.FlowIndentStable.scanKey_indents_of_inFlow hf hok
    have hcols : s'.indentColumns = s.indentColumns := by simp [ScannerState.indentColumns, hind]
    have hinn : s'.innermostPendingKey = s.innermostPendingKey := by
      rw [innermostPendingKey_eq, innermostPendingKey_eq, hcols, hpk]
    have hpos : 0 < s.flowLevel := by simpa [ScannerState.inFlow] using hf
    refine ⟨⟨by rw [hpk, hind]; exact hs.1, ?_⟩, ?_, ?_, ?_⟩
    · intro i l hi; rw [hcols]; exact hs.2 i l (hpk ▸ hi)
    · intro h0; rw [hfl] at h0; omega
    · intro _; rw [hstk, hinn]; exact hb hpos
    · show s'.explicitKeyStack.size = s'.flowLevel; rw [hstk, hfl]; exact hst
  · have h_noflow : s.inFlow = false := by simpa using hf
    have h0 : s.flowLevel = 0 := (inFlow_false_iff s).1 h_noflow
    have hind := L4YAML.Proofs.PreprocessIndentStable.scanKey_indents h_noflow hok
    have hpk := scanKey_pendingKeys h_noflow hok
    obtain ⟨sp, hsp⟩ : ∃ sp, sp = pushMappingIndent s (s.col : Int) := ⟨_, rfl⟩
    rw [← hsp] at hind hpk
    have hsl : SlotsOk sp := hsp ▸ pushMappingIndent_slots s _ hs
    have hsz := hsl.1
    have hpos : 0 < sp.indents.size :=
      hsp ▸ (L4YAML.Proofs.IndentStackBase.pushMappingIndent_base s _ hbase).size_pos
    -- the top of the pushed stack is the `?`'s own column
    have htop_ci : sp.currentIndent = (s.col : Int) := by
      rw [hsp]
      exact Int.le_antisymm (L4YAML.Proofs.IndentStackCover.pushMappingIndent_top_le (hcol h_noflow))
        (L4YAML.Proofs.PreprocessIndentStable.pushMappingIndent_le s _)
    have htop : sp.indentColumns[sp.indents.size - 1]? = some (s.col : Int) := by
      rw [indentColumns_getElem?, Array.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some]
      rw [← L4YAML.Proofs.IndentStackMono.currentIndent_eq_last hpos, htop_ci]
    have hcols' : s'.indentColumns = sp.indentColumns := by
      simp [ScannerState.indentColumns, hind]
    have hinn : s'.innermostPendingKey = (some s.line, (s.col : Int)) := by
      rw [innermostPendingKey_eq, hcols', hpk, ← hsz,
        innermost_set_top _ _ _ (by rw [indentColumns_size]; exact hsz.symm) (by omega)]
      rw [hsz, htop]; rfl
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hpk, hind, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hsz
    · intro i l hi
      rw [hpk, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hi
      rw [hcols']
      split at hi
      · rename_i heq
        subst heq
        exact ⟨(s.col : Int), htop, by omega⟩
      · exact hsl.2 i l hi
    · intro _; rw [hekl, hekc, hinn]
    · intro hpos'; rw [hfl] at hpos'; omega
    · show s'.explicitKeyStack.size = s'.flowLevel; rw [hstk, hfl]; exact hst

lemma scanValueClearKey_core (s : ScannerState) :
    (scanValueClearKey s).indents = s.indents ∧ (scanValueClearKey s).pendingKeys = s.pendingKeys ∧
    (scanValueClearKey s).flowLevel = s.flowLevel ∧
    (scanValueClearKey s).explicitKeyLine = s.explicitKeyLine ∧
    (scanValueClearKey s).explicitKeyCol = s.explicitKeyCol ∧
    (scanValueClearKey s).explicitKeyStack = s.explicitKeyStack := by
  unfold scanValueClearKey
  split <;> (try split) <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `scanValuePrepare` pushes at most one empty slot: `SlotsOk` and the innermost
    pending key survive, as do the flow fields and the register. -/
lemma scanValuePrepare_core (s : ScannerState) (hs : SlotsOk s) :
    SlotsOk (scanValuePrepare s) ∧
    (scanValuePrepare s).innermostPendingKey = s.innermostPendingKey ∧
    (scanValuePrepare s).flowLevel = s.flowLevel ∧
    (scanValuePrepare s).explicitKeyLine = s.explicitKeyLine ∧
    (scanValuePrepare s).explicitKeyCol = s.explicitKeyCol ∧
    (scanValuePrepare s).explicitKeyStack = s.explicitKeyStack := by
  unfold scanValuePrepare
  split
  · split
    · split
      · refine ⟨hs.push_none { column := (s.simpleKey.pos.col : Int), isSequence := false } rfl rfl,
          ?_, rfl, rfl, rfl, rfl⟩
        rw [innermostPendingKey_eq, innermostPendingKey_eq]
        simp only [ScannerState.indentColumns, Array.map_push]
        exact innermost_push_none _ _ _ (by simp [hs.1])
      · exact ⟨hs, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨hs, rfl, rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨hs, rfl, rfl, rfl, rfl, rfl⟩
    · split
      · refine ⟨pushMappingIndent_slots s _ hs, ?_, ?_, ?_, ?_, ?_⟩ <;>
          unfold pushMappingIndent <;> split <;> try rfl
        rw [innermostPendingKey_eq, innermostPendingKey_eq]
        simp only [ScannerState.indentColumns, ScannerState.emit, Array.map_push]
        exact innermost_push_none _ _ _ (by simp [hs.1])
      · exact ⟨hs, rfl, rfl, rfl, rfl, rfl⟩

lemma innermost_none_snd (cols : Array Int) (pks : Array (Option Nat))
    (h : (PendingKeys.innermost cols pks).1 = none) : (PendingKeys.innermost cols pks).2 = -1 := by
  rw [innermost_eq_go] at h ⊢; exact go_none_snd cols pks _ h

lemma scanValue_sound {s s' : ScannerState} (hok : scanValue s = .ok s') (h : Sound s) :
    Sound s' := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok; subst hok
  obtain ⟨hck1, hck2, hck3, hck4, hck5, hck6⟩ := scanValueClearKey_core s
  have hs_kc : SlotsOk (scanValueClearKey s) := by
    refine ⟨by rw [hck1, hck2]; exact h.slots.1, ?_⟩
    intro i l hi; rw [hck2] at hi
    have hcols : (scanValueClearKey s).indentColumns = s.indentColumns := by
      simp [ScannerState.indentColumns, hck1]
    rw [hcols]; exact h.slots.2 i l hi
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := scanValuePrepare_core _ hs_kc
  have hinn_kc : (scanValueClearKey s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, ScannerState.indentColumns, hck1, hck2]
  -- the emitted-and-advanced state before the final write
  have hadv_pk : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).pendingKeys
      = (scanValuePrepare (scanValueClearKey s)).pendingKeys := by
    rw [advance_preserves_pendingKeys, emit_pendingKeys]
  have hadv_ind : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indents
      = (scanValuePrepare (scanValueClearKey s)).indents := by
    rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]; rfl
  have hadv_cols : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indentColumns
      = (scanValuePrepare (scanValueClearKey s)).indentColumns := by
    simp [ScannerState.indentColumns, hadv_ind]
  have hadv_fl : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).flowLevel
      = s.flowLevel := by
    rw [L4YAML.Proofs.ScannerLoopInvariant.advance_flowLevel]; simp [ScannerState.emit, ScannerState.emitAt, hp3, hck3]
  have hadv_st : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).explicitKeyStack
      = s.explicitKeyStack := by
    rw [L4YAML.Proofs.ScannerEkStack.advance_preserves_explicitKeyStack,
        L4YAML.Proofs.ScannerEkStack.emit_preserves_explicitKeyStack, hp6, hck6]
  have hadv_inn : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).innermostPendingKey
      = s.innermostPendingKey := by
    rw [innermostPendingKey_eq, hadv_cols, hadv_pk, ← innermostPendingKey_eq, hp2, hinn_kc]
  have hadv_slots : SlotsOk (((scanValuePrepare (scanValueClearKey s)).emit .value).advance) := by
    refine ⟨by rw [hadv_pk, hadv_ind]; exact hp1.1, ?_⟩
    intro i l hi; rw [hadv_pk] at hi; rw [hadv_cols]; exact hp1.2 i l hi
  by_cases hf : s.inFlow = true
  · -- flow: the `:` ends any pending key; the stack and the slots are untouched
    have hpos : 0 < s.flowLevel := by simpa [ScannerState.inFlow] using hf
    simp only [hf, Bool.true_or, ite_true]
    refine ⟨⟨hadv_slots.1, hadv_slots.2⟩, ?_, ?_, ?_⟩
    · intro h0; simp only [hadv_fl] at h0; omega
    · intro _
      change ((((scanValuePrepare (scanValueClearKey s)).emit .value).advance).explicitKeyStack)[0]? = some (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).innermostPendingKey
      rw [hadv_st, hadv_inn]; exact h.base hpos
    · show _ = _; rw [hadv_st, hadv_fl]; exact h.stack
  · have h_noflow : s.inFlow = false := by simpa using hf
    have h0 : s.flowLevel = 0 := (inFlow_false_iff s).1 h_noflow
    simp only [h_noflow, Bool.false_eq_true, ↓reduceIte]
    by_cases hsv : scanValueKeySurvives s (scanValueClearKey s) = true
    · simp only [hsv, ↓reduceIte]
      refine ⟨⟨hadv_slots.1, hadv_slots.2⟩, ?_, ?_, ?_⟩
      · intro _
        change (_, _) = (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).innermostPendingKey
        rw [hck4, hck5, hadv_inn, ← h.reg h0]
        cases hek : s.explicitKeyLine with
        | some l => rfl
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          have := innermost_none_snd s.indentColumns s.pendingKeys
            (by rw [← innermostPendingKey_eq, ← h.reg h0, hek])
          rw [← innermostPendingKey_eq, ← h.reg h0] at this
          simp only at this; rw [this]
      · intro hpos; simp only [hadv_fl] at hpos; omega
      · show _ = _; rw [hadv_st, hadv_fl]; exact h.stack
    · simp only [hsv, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · show (PendingKeys.closeAt _ _ _).size = _
        rw [closeAt_size]; exact hadv_slots.1
      · intro i l hi
        obtain ⟨hm, -⟩ := closeAt_marked _ _ _ _ _ hi
        exact hadv_slots.2 i l hm
      · intro _; rfl
      · intro hpos; simp only [hadv_fl] at hpos; omega
      · show _ = _; rw [hadv_st, hadv_fl]; exact h.stack

/-- Inside flow the register is not read by `Sound`; transport along a step that
    keeps the slots, the frames, the flow level and the saved pairs. -/
lemma Sound.of_eq_inFlow {s s' : ScannerState} (h : Sound s) (hpos : 0 < s.flowLevel)
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents)
    (hfl : s'.flowLevel = s.flowLevel) (hst : s'.explicitKeyStack = s.explicitKeyStack) :
    Sound s' := by
  have hcols : s'.indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : s'.innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0; rw [hfl] at h0; omega
  · intro _; rw [hst, hinn]; exact h.base hpos
  · show s'.explicitKeyStack.size = s'.flowLevel
    rw [hst, hfl]; exact h.stack

lemma pushSequenceIndent_flowLevel (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).flowLevel = s.flowLevel := by
  unfold pushSequenceIndent; split <;> rfl

lemma pushSequenceIndent_explicitKeyLine (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).explicitKeyLine = s.explicitKeyLine := by
  unfold pushSequenceIndent; split <;> rfl

lemma pushSequenceIndent_explicitKeyCol (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).explicitKeyCol = s.explicitKeyCol := by
  unfold pushSequenceIndent; split <;> rfl

lemma pushSequenceIndent_explicitKeyStack (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).explicitKeyStack = s.explicitKeyStack := by
  unfold pushSequenceIndent; split <;> rfl

lemma scanBlockEntry_pendingKeys {s s' : ScannerState} (hnf : s.inFlow = false)
    (hok : scanBlockEntry s = .ok s') :
    s'.pendingKeys = (pushSequenceIndent s (s.col : Int)).pendingKeys := by
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind, hnf, Bool.not_false, if_true] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals simp [advance_preserves_pendingKeys, emit_pendingKeys]

/-- `-` in block context: the sequence level is pushed (empty slot), the
    register and the saved pairs are untouched. -/
lemma scanBlockEntry_sound {s s' : ScannerState} (hnf : s.inFlow = false)
    (hok : scanBlockEntry s = .ok s') (h : Sound s) : Sound s' := by
  obtain ⟨hekl, hekc⟩ := L4YAML.Proofs.ExplicitKeyCoupling.scanBlockEntry_preserves_explicitKey hok
  refine Sound.of_eq (pushSequenceIndent_sound s (s.col : Int) h)
    (scanBlockEntry_pendingKeys hnf hok)
    (L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents hnf hok) ?_ ?_ ?_ ?_
  · rw [pushSequenceIndent_flowLevel]
    exact L4YAML.Proofs.ScannerCorrectness.scanBlockEntry_preserves_flowLevel s s' hok
  · rw [pushSequenceIndent_explicitKeyLine]; exact hekl
  · rw [pushSequenceIndent_explicitKeyCol]; exact hekc
  · rw [pushSequenceIndent_explicitKeyStack]
    exact L4YAML.Proofs.ScannerEkStack.scanBlockEntry_preserves_explicitKeyStack s s' hok

/-- Opening a flow collection saves the register pair on the stack and clears
    the register.  At depth 0 the saved pair is the innermost pending key
    (`RegOk`); deeper, slot 0 of the stack is untouched (`BaseOk`). -/
lemma scanFlowSequenceStart_sound (s : ScannerState) (h : Sound s) :
    Sound (scanFlowSequenceStart s) := by
  have hpk := scanFlowSequenceStart_preserves_pendingKeys s
  have hind : (scanFlowSequenceStart s).indents = s.indents := by
    unfold scanFlowSequenceStart
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit,
      ScannerState.emitAt]
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowSequenceStart_ek_pushed s
  have hfl := L4YAML.Proofs.ScannerContracts.scanFlowSequenceStart_flowLevel s
  have hcols : (scanFlowSequenceStart s).indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : (scanFlowSequenceStart s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  have hsz : s.explicitKeyStack.size = s.flowLevel := h.stack
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0; rw [hfl] at h0; omega
  · intro _
    rw [hst, hinn, Array.getElem?_push]
    rcases Nat.eq_zero_or_pos s.flowLevel with h0 | hpos
    · rw [if_pos (by omega), h.reg h0]
    · rw [if_neg (by omega)]; exact h.base hpos
  · show (scanFlowSequenceStart s).explicitKeyStack.size = (scanFlowSequenceStart s).flowLevel
    rw [hst, hfl, Array.size_push, hsz]

lemma scanFlowMappingStart_sound (s : ScannerState) (h : Sound s) :
    Sound (scanFlowMappingStart s) := by
  have hpk := scanFlowMappingStart_preserves_pendingKeys s
  have hind : (scanFlowMappingStart s).indents = s.indents := by
    unfold scanFlowMappingStart
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit,
      ScannerState.emitAt]
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowMappingStart_ek_pushed s
  have hfl := L4YAML.Proofs.ScannerContracts.scanFlowMappingStart_flowLevel s
  have hcols : (scanFlowMappingStart s).indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : (scanFlowMappingStart s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  have hsz : s.explicitKeyStack.size = s.flowLevel := h.stack
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0; rw [hfl] at h0; omega
  · intro _
    rw [hst, hinn, Array.getElem?_push]
    rcases Nat.eq_zero_or_pos s.flowLevel with h0 | hpos
    · rw [if_pos (by omega), h.reg h0]
    · rw [if_neg (by omega)]; exact h.base hpos
  · show (scanFlowMappingStart s).explicitKeyStack.size = (scanFlowMappingStart s).flowLevel
    rw [hst, hfl, Array.size_push, hsz]

/-- Closing a flow collection restores the saved pair.  Back at depth 0 the
    restored pair is slot 0 (`BaseOk` of the opener); deeper, slot 0 survives
    the pop. -/
lemma scanFlowSequenceEnd_sound (s : ScannerState) (h : Sound s) (hpos : 0 < s.flowLevel) :
    Sound (scanFlowSequenceEnd s) := by
  have hpk := scanFlowSequenceEnd_preserves_pendingKeys s
  have hind : (scanFlowSequenceEnd s).indents = s.indents := by
    unfold scanFlowSequenceEnd; dsimp only []
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit]
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowSequenceEnd_ekstack_popped s
  have hfl := L4YAML.Proofs.ScannerFlowCollection.scanFlowSequenceEnd_flowLevel_pos s hpos
  have hreg : ((scanFlowSequenceEnd s).explicitKeyLine, (scanFlowSequenceEnd s).explicitKeyCol)
      = s.explicitKeyStack.back?.getD (none, -1) := rfl
  have hcols : (scanFlowSequenceEnd s).indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : (scanFlowSequenceEnd s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  have hsz : s.explicitKeyStack.size = s.flowLevel := h.stack
  have hb := h.base hpos
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0
    rw [hfl] at h0
    have h1 : s.explicitKeyStack.size - 1 = 0 := by omega
    rw [hreg, hinn, Array.back?, h1, hb]; rfl
  · intro hpos'
    rw [hfl] at hpos'
    rw [hst, hinn, Array.getElem?_pop, if_pos (by omega)]; exact hb
  · show (scanFlowSequenceEnd s).explicitKeyStack.size = (scanFlowSequenceEnd s).flowLevel
    rw [hst, hfl, Array.size_pop, hsz]

lemma scanFlowMappingEnd_sound (s : ScannerState) (h : Sound s) (hpos : 0 < s.flowLevel) :
    Sound (scanFlowMappingEnd s) := by
  have hpk := scanFlowMappingEnd_preserves_pendingKeys s
  have hind : (scanFlowMappingEnd s).indents = s.indents := by
    unfold scanFlowMappingEnd; dsimp only []
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit]
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowMappingEnd_ekstack_popped s
  have hfl := L4YAML.Proofs.ScannerFlowCollection.scanFlowMappingEnd_flowLevel_pos s hpos
  have hreg : ((scanFlowMappingEnd s).explicitKeyLine, (scanFlowMappingEnd s).explicitKeyCol)
      = s.explicitKeyStack.back?.getD (none, -1) := rfl
  have hcols : (scanFlowMappingEnd s).indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : (scanFlowMappingEnd s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  have hsz : s.explicitKeyStack.size = s.flowLevel := h.stack
  have hb := h.base hpos
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0
    rw [hfl] at h0
    have h1 : s.explicitKeyStack.size - 1 = 0 := by omega
    rw [hreg, hinn, Array.back?, h1, hb]; rfl
  · intro hpos'
    rw [hfl] at hpos'
    rw [hst, hinn, Array.getElem?_pop, if_pos (by omega)]; exact hb
  · show (scanFlowMappingEnd s).explicitKeyStack.size = (scanFlowMappingEnd s).flowLevel
    rw [hst, hfl, Array.size_pop, hsz]

/-- `,` is dispatched only inside flow (`flowEndOutsideFlow` otherwise); it
    clears the register line, which `Sound` does not read there. -/
lemma scanFlowEntry_sound {s s' : ScannerState} (hok : scanFlowEntry s = .ok s') (h : Sound s)
    (hpos : 0 < s.flowLevel) : Sound s' :=
  Sound.of_eq_inFlow h hpos (scanFlowEntry_preserves_pendingKeys hok)
    (L4YAML.Proofs.FlowIndentStable.scanFlowEntry_preserves_indents hok)
    (L4YAML.Proofs.ScannerFlowCollection.scanFlowEntry_preserves_flowLevel s s' hok)
    (L4YAML.Proofs.ScannerEkStack.scanFlowEntry_preserves_explicitKeyStack s s' hok)

/-! ### Document markers: unwinding to the sentinel leaves no marked slot -/

lemma unwindIndents_slots (s : ScannerState) (col : Int) (h : SlotsOk s) :
    SlotsOk (unwindIndents s col) := by
  unfold unwindIndents; exact unwindIndentsLoop_slots s col _ h

/-- Unwinding to `-1` on a monotone sentinel-based stack pops every level with a
    column ≥ 0, hence (by `SlotsOk`) every marked slot: the innermost pending
    key reads `(none, -1)`. -/
lemma unwindIndents_neg_innermost {s : ScannerState} (hs : SlotsOk s) (hm : Mono s)
    (hbase : SentinelBase s) :
    (unwindIndents s (-1)).innermostPendingKey = (none, -1) := by
  have hs' := unwindIndents_slots s (-1) hs
  have hm' : Mono (unwindIndents s (-1)) := L4YAML.Proofs.IndentStackMono.unwindIndents_mono s (-1) hm
  have hb' : SentinelBase (unwindIndents s (-1)) :=
    L4YAML.Proofs.IndentStackBase.unwindIndents_base s (-1) hbase
  have htop : (unwindIndents s (-1)).currentIndent ≤ -1 := by
    rcases L4YAML.Proofs.PreprocessIndentStable.unwindIndents_terminal s (-1) with h1 | h2
    · exact h1
    · rw [hb'.currentIndent_of_size_le_one h2]; exact Int.le_refl _
  have hnone : ∀ (i l : Nat), (unwindIndents s (-1)).pendingKeys[i]? = some (some l) → False := by
    intro i l hi
    obtain ⟨c, hc, hc0⟩ := hs'.2 i l hi
    simp only [ScannerState.indentColumns, Array.getElem?_map, Option.map_eq_some_iff] at hc
    obtain ⟨e, he, hec⟩ := hc
    have hle := hm'.le_currentIndent e (Array.mem_of_getElem? he)
    omega
  rcases hinn : (unwindIndents s (-1)).innermostPendingKey with ⟨ol, c⟩
  rcases ol with _ | l
  · rw [innermostPendingKey_eq, innermost_eq_go] at hinn
    have h2 := go_none_snd _ _ _ (by rw [hinn])
    rw [hinn] at h2
    simp only at h2
    rw [h2]
  · exfalso
    rw [innermostPendingKey_eq] at hinn
    obtain ⟨i, _, hi, _⟩ := innermost_some_mem _ _ l c hinn
    exact hnone i l hi

/-- The shape both document markers share: unwind to the sentinel, reset the
    register, keep the saved pairs (empty at depth 0). -/
lemma Sound.of_doc_reset {s s' : ScannerState} (h : Sound s) (hfl : s.flowLevel = 0)
    (hm : Mono s) (hbase : SentinelBase s)
    (hpk : s'.pendingKeys = (unwindIndents s (-1)).pendingKeys)
    (hind : s'.indents = (unwindIndents s (-1)).indents)
    (hfl' : s'.flowLevel = s.flowLevel)
    (hekl : s'.explicitKeyLine = none) (hekc : s'.explicitKeyCol = -1)
    (hst : s'.explicitKeyStack = s.explicitKeyStack) : Sound s' := by
  have hs' := unwindIndents_slots s (-1) h.slots
  have hinn0 := unwindIndents_neg_innermost h.slots hm hbase
  have hcols : s'.indentColumns = (unwindIndents s (-1)).indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : s'.innermostPendingKey = (none, -1) := by
    rw [innermostPendingKey_eq, hcols, hpk, ← innermostPendingKey_eq, hinn0]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact hs'.1
  · intro i l hi; rw [hcols]; exact hs'.2 i l (hpk ▸ hi)
  · intro _; rw [hekl, hekc, hinn]
  · intro h0; rw [hfl', hfl] at h0; omega
  · show s'.explicitKeyStack.size = s'.flowLevel
    rw [hst, hfl', h.stack]

lemma scanDocumentStart_sound (s : ScannerState) (h : Sound s) (hfl : s.flowLevel = 0)
    (hm : Mono s) (hbase : SentinelBase s) : Sound (scanDocumentStart s) := by
  refine Sound.of_doc_reset h hfl hm hbase ?_ ?_ ?_ rfl rfl
    (L4YAML.Proofs.ScannerEkStack.scanDocumentStart_preserves_explicitKeyStack s)
  · unfold scanDocumentStart; simp [advanceN_preserves_pendingKeys, emit_pendingKeys]
  · unfold scanDocumentStart
    simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents,
      L4YAML.Proofs.ScannerContracts.emit_indents]
  · unfold scanDocumentStart
    simp [L4YAML.Proofs.ScannerCorrectness.advanceN_preserves_flowLevel, ScannerState.emit,
      ScannerState.emitAt, L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_flowLevel]

lemma scanDocumentEnd_sound {s s' : ScannerState} (hok : scanDocumentEnd s = .ok s') (h : Sound s)
    (hfl : s.flowLevel = 0) (hm : Mono s) (hbase : SentinelBase s) : Sound s' := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals
    refine Sound.of_doc_reset h hfl hm hbase ?_ ?_ ?_ rfl rfl ?_
  all_goals (try simp [advanceN_preserves_pendingKeys, emit_pendingKeys])
  all_goals (try simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents,
      L4YAML.Proofs.ScannerContracts.emit_indents])
  all_goals (try simp [L4YAML.Proofs.ScannerCorrectness.advanceN_preserves_flowLevel,
      ScannerState.emit, ScannerState.emitAt,
      L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_flowLevel])
  all_goals simp [L4YAML.Proofs.ScannerEkStack.advanceN_preserves_explicitKeyStack,
      L4YAML.Proofs.ScannerEkStack.emit_preserves_explicitKeyStack,
      L4YAML.Proofs.ScannerEkStack.unwindIndents_preserves_explicitKeyStack]

/-! ## §4  The preprocess and the dispatchers -/

/-- The preprocess keeps everything but `RegOk`, and keeps `RegOk` unless the
    next character is a `?` — the one hook exemption that can outlive the pop
    of the key's level (`- ? a⏎? b`); `scanKey` overwrites the register. -/
lemma preprocess_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : Sound s)
    (hm : Mono s) (hbase : SentinelBase s) :
    SlotsOk s' ∧ BaseOk s' ∧ StackOk s' ∧ (c ≠ '?' → RegOk s') := by
  sorry

lemma dispatchStructural_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchStructural s c = .ok (some s')) (h : Sound s)
    (hm : Mono s) (hbase : SentinelBase s) : Sound s' := by
  sorry

lemma dispatchFlowIndicators_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) (h : Sound s) : Sound s' := by
  sorry

lemma dispatchBlockIndicators_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (hs : SlotsOk s) (hb : BaseOk s) (hst : StackOk s) (hr : c ≠ '?' → RegOk s)
    (hbase : SentinelBase s) : Sound s' := by
  sorry

lemma dispatchContent_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') (h : Sound s) : Sound s' := by
  sorry

/-! ## §5  The step and the seed -/

/-- **The step keeps the register honest.** -/
lemma scanNextToken_sound {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s')) (h : Sound s) (hm : Mono s) (hbase : SentinelBase s) :
    Sound s' := by
  sorry

/-! ### The seed -/

lemma mk'_sound (input : String) : Sound (ScannerState.mk' input) := by
  refine ⟨⟨rfl, ?_⟩, ?_, ?_, rfl⟩
  · intro i l hi
    rcases i with _ | i
    · simp [ScannerState.mk'] at hi
    · simp [ScannerState.mk'] at hi
  · intro _
    show ((none : Option Nat), (-1 : Int)) = PendingKeys.innermost _ _
    rw [innermost_eq_go]; rfl
  · intro h; simp [ScannerState.mk'] at h

end L4YAML.Proofs.PendingKeySound

end Blanket
