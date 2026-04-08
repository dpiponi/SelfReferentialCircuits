import Bitstream.Letterless

namespace Bitstream

namespace LetterlessFormula

theorem eval_axiom1 (a b : LetterlessFormula) :
    eval (a ⇒ (b ⇒ a)) = const1 := by
  funext t
  cases ha : eval a t <;> cases hb : eval b t <;>
    simp [eval, bimplies, const1, const, ha, hb]

theorem eval_axiom2 (a b c : LetterlessFormula) :
    eval ((a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))) = const1 := by
  funext t
  cases ha : eval a t <;> cases hb : eval b t <;> cases hc : eval c t <;>
    simp [eval, bimplies, const1, const, ha, hb, hc]

theorem eval_axiom_classical (a : LetterlessFormula) :
    eval (((a ⇒ ⊥) ⇒ ⊥) ⇒ a) = const1 := by
  funext t
  cases ha : eval a t <;>
    simp [eval, bimplies, const1, const, const0, const, ha]

theorem eval_box_of_true (a : LetterlessFormula) (h : eval a = const1) :
    eval (□a) = const1 := by
  simpa [eval, h] using box_const1

theorem box_lob_axiom_true (s : Bitstream) :
    (Bitstream.box (Bitstream.box s =⇒ s) =⇒ Bitstream.box s) = const1 := by
  funext t
  by_cases hante : Bitstream.box (Bitstream.box s =⇒ s) t = true
  · have hprefix :
        ∀ k, k < t → (Bitstream.box s =⇒ s) k = true :=
        (box_eq_true_iff_prefix_all_true (Bitstream.box s =⇒ s) t).mp hante
    have hboxPrefix : ∀ k, k ≤ t → Bitstream.box s k = true := by
      intro k hk
      induction k with
      | zero =>
          rfl
      | succ k ih =>
          have hk' : k < t := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
          have hboxk : Bitstream.box s k = true := ih (Nat.le_of_lt hk')
          have himpk : (Bitstream.box s =⇒ s) k = true := hprefix k hk'
          have hsk : s k = true := by
            cases hs : s k with
            | false =>
                simp [bimplies, hboxk, hs] at himpk
            | true =>
                simp
          simp [Bitstream.box, hboxk, hsk]
    have hboxt : Bitstream.box s t = true := by
      apply (box_eq_true_iff_prefix_all_true s t).2
      intro k hk
      have hboxk : Bitstream.box s k = true := hboxPrefix k (Nat.le_of_lt hk)
      have himpk : (Bitstream.box s =⇒ s) k = true := hprefix k hk
      cases hs : s k with
      | false =>
          simp [bimplies, hboxk, hs] at himpk
      | true =>
          simp
    simp [bimplies, hante, hboxt, const1, const]
  · simp [bimplies, hante, const1, const]

theorem eval_lob_axiom (a : LetterlessFormula) :
    eval (□(□a ⇒ a) ⇒ □a) = const1 := by
  simpa [eval] using box_lob_axiom_true (eval a)

end LetterlessFormula

/-
This file uses a Hilbert-style system with necessitation and the standard
Löb axiom

  □(□A ⇒ A) ⇒ □A

rather than a separate Löb rule.
-/
inductive Provable : LetterlessFormula → Prop
  | axiom1 (a b : LetterlessFormula) :
      Provable (a ⇒ (b ⇒ a))
  | axiom2 (a b c : LetterlessFormula) :
      Provable ((a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c)))
  | axiomClassical (a : LetterlessFormula) :
      Provable (((a ⇒ ⊥) ⇒ ⊥) ⇒ a)
  | axiomK (a b : LetterlessFormula) :
      Provable (□(a ⇒ b) ⇒ (□a ⇒ □b))
  | axiomLob (a : LetterlessFormula) :
      Provable (□(□a ⇒ a) ⇒ □a)
  | modusPonens {a b : LetterlessFormula} :
      Provable (a ⇒ b) → Provable a → Provable b
  | necessitation {a : LetterlessFormula} :
      Provable a → Provable (□a)

theorem provable_sound {a : LetterlessFormula} (h : Provable a) :
    LetterlessFormula.eval a = const1 := by
  refine Provable.rec (motive := fun {a} _ => LetterlessFormula.eval a = const1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro a b
    exact LetterlessFormula.eval_axiom1 a b
  · intro a b c
    exact LetterlessFormula.eval_axiom2 a b c
  · intro a
    exact LetterlessFormula.eval_axiom_classical a
  · intro a b
    simpa [LetterlessFormula.eval] using box_implication_distributes_true
      (LetterlessFormula.eval a) (LetterlessFormula.eval b)
  · intro a
    exact LetterlessFormula.eval_lob_axiom a
  · intro a b hab ha ihab iha
    funext t
    have hImp : LetterlessFormula.eval (a ⇒ b) t = true := by
      simpa [const1, const] using congrArg (fun f => f t) ihab
    have hA : LetterlessFormula.eval a t = true := by
      simpa [const1, const] using congrArg (fun f => f t) iha
    have hB : LetterlessFormula.eval b t = true := by
      simpa [LetterlessFormula.eval, bimplies, hA] using hImp
    simpa [const1, const] using hB
  · intro a ha iha
    exact LetterlessFormula.eval_box_of_true a iha

theorem soundness (a : LetterlessFormula) :
    Provable a → LetterlessFormula.eval a = const1 :=
  provable_sound

end Bitstream
