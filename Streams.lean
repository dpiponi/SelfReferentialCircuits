namespace Bitstream

open Classical

abbrev Bit : Type := Bool
abbrev Time : Type := Nat
abbrev Bitstream : Type := Time → Bit

def bnot : Bitstream → Bitstream := fun s t => !(s t)
def band : Bitstream → Bitstream → Bitstream := fun s₁ s₂ t => s₁ t && s₂ t
def bor : Bitstream → Bitstream → Bitstream := fun s₁ s₂ t => s₁ t || s₂ t
def bimplies : Bitstream → Bitstream → Bitstream := fun s₁ s₂ t => !(s₁ t) || s₂ t

prefix:max "∼" => bnot
infixr:70 " &&& " => band
infixr:65 " ||| " => bor
infixr:60 " =⇒ " => bimplies

def box (s : Bitstream) : Bitstream
  | 0 => true
  | t + 1 => box s t && s t

def const (b : Bit) : Bitstream := fun _ => b

def const0 : Bitstream := const false
def const1 : Bitstream := const true
def EventuallyConstant (s : Bitstream) : Prop := ∃ N : Nat, ∃ b : Bit, ∀ t, N ≤ t → s t = b
def pulse : Bitstream
  | 0 => true
  | _ + 1 => false

theorem const_eventuallyConstant (b : Bit) : EventuallyConstant (const b) := by
  refine ⟨0, b, ?_⟩
  intro t _
  rfl

theorem const0_eventuallyConstant : EventuallyConstant const0 :=
  const_eventuallyConstant false

theorem const1_eventuallyConstant : EventuallyConstant const1 :=
  const_eventuallyConstant true

theorem box_zero (s : Bitstream) : box s 0 = true := rfl

theorem box_succ (s : Bitstream) (t : Time) : box s (t + 1) = (box s t && s t) := rfl

theorem box_succ_of_input_false {s : Bitstream} {t : Time} (h : s t = false) :
    box s (t + 1) = false := by
  simp [box, h]

theorem box_succ_of_box_false {s : Bitstream} {t : Time} (h : box s t = false) :
    box s (t + 1) = false := by
  simp [box, h]

theorem box_stays_false {s : Bitstream} {t : Time} (h : box s t = false) :
    ∀ u : Time, box s (t + u) = false
  | 0 => by simpa using h
  | u + 1 => by
      have ih : box s (t + u) = false := box_stays_false h u
      have step : box s ((t + u) + 1) = false := box_succ_of_box_false ih
      simpa [Nat.add_assoc] using step

theorem box_const1 : box const1 = const1 := by
  funext t
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      simpa [box, const1, const] using ih

theorem box_eq_true_iff_prefix_all_true (s : Bitstream) (t : Time) :
    box s t = true ↔ ∀ k, k < t → s k = true := by
  induction t with
  | zero =>
      constructor
      · intro _
        intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      · intro _
        rfl
  | succ t ih =>
      constructor
      · intro h
        intro k hk
        have hk' : k < t ∨ k = t := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk)
        cases hk' with
        | inl hlt =>
            have hbox : box s t = true := by
              cases hs : s t <;> simp [box, hs] at h
              exact h
            exact (ih.mp hbox) k hlt
        | inr heq =>
            cases hs : s t <;> simp [box, hs] at h
            exact heq ▸ hs
      · intro h
        have hbox : box s t = true := by
          exact ih.mpr (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self t)))
        have hs : s t = true := h t (Nat.lt_succ_self t)
        simp [box, hbox, hs]

theorem box_eventuallyConstant (s : Bitstream) : EventuallyConstant (box s) := by
  by_cases hall : ∀ t, s t = true
  · refine ⟨0, true, ?_⟩
    intro t _
    have hs : s = const1 := by
      funext u
      simpa [const1, const] using hall u
    have hbox : box s = const1 := by
      simpa [hs] using box_const1
    simpa [const1, const] using congrArg (fun f => f t) hbox
  · have hfalse : ∃ t, s t = false := by
      refine Classical.byContradiction ?_
      intro h
      apply hall
      intro t
      cases hbit : s t with
      | false =>
          exact False.elim (h ⟨t, hbit⟩)
      | true =>
          simp
    rcases hfalse with ⟨t, ht⟩
    refine ⟨t + 1, false, ?_⟩
    intro u hu
    have hbox : box s (t + 1) = false := box_succ_of_input_false ht
    have hwitness : ∃ k, u = (t + 1) + k := ⟨u - (t + 1), (Nat.add_sub_of_le hu).symm⟩
    rcases hwitness with ⟨k, rfl⟩
    exact box_stays_false hbox k

theorem bnot_eventuallyConstant {s : Bitstream} (hs : EventuallyConstant s) :
    EventuallyConstant (∼s) := by
  rcases hs with ⟨N, b, hb⟩
  refine ⟨N, !b, ?_⟩
  intro t ht
  simp [bnot, hb t ht]

theorem band_eventuallyConstant {s t : Bitstream}
    (hs : EventuallyConstant s) (ht : EventuallyConstant t) :
    EventuallyConstant (s &&& t) := by
  rcases hs with ⟨Ns, bs, hs'⟩
  rcases ht with ⟨Nt, bt, ht'⟩
  refine ⟨max Ns Nt, bs && bt, ?_⟩
  intro u hu
  have hus : Ns ≤ u := Nat.le_trans (Nat.le_max_left _ _) hu
  have hut : Nt ≤ u := Nat.le_trans (Nat.le_max_right _ _) hu
  simp [band, hs' u hus, ht' u hut]

theorem bor_eventuallyConstant {s t : Bitstream}
    (hs : EventuallyConstant s) (ht : EventuallyConstant t) :
    EventuallyConstant (s ||| t) := by
  rcases hs with ⟨Ns, bs, hs'⟩
  rcases ht with ⟨Nt, bt, ht'⟩
  refine ⟨max Ns Nt, bs || bt, ?_⟩
  intro u hu
  have hus : Ns ≤ u := Nat.le_trans (Nat.le_max_left _ _) hu
  have hut : Nt ≤ u := Nat.le_trans (Nat.le_max_right _ _) hu
  simp [bor, hs' u hus, ht' u hut]

theorem bimplies_eventuallyConstant {s t : Bitstream}
    (hs : EventuallyConstant s) (ht : EventuallyConstant t) :
    EventuallyConstant (s =⇒ t) := by
  rcases hs with ⟨Ns, bs, hs'⟩
  rcases ht with ⟨Nt, bt, ht'⟩
  refine ⟨max Ns Nt, (!bs) || bt, ?_⟩
  intro u hu
  have hus : Ns ≤ u := Nat.le_trans (Nat.le_max_left _ _) hu
  have hut : Nt ≤ u := Nat.le_trans (Nat.le_max_right _ _) hu
  simp [bimplies, hs' u hus, ht' u hut]

end Bitstream
