import Bitstream.ProofSystem
import Bitstream.Guarded

namespace Bitstream

namespace Provable

/--
Provable equivalence in the Hilbert system.
-/
def Eqv (a b : LetterlessFormula) : Prop :=
  Provable (a ⇒ b) ∧ Provable (b ⇒ a)

/--
From a provable formula `b`, we may prove `a ⇒ b`.
-/
theorem weaken {a b : LetterlessFormula} (hb : Provable b) :
    Provable (a ⇒ b) :=
  Provable.modusPonens (Provable.axiom1 b a) hb

/--
Hilbert-style derivation of `a ⇒ a`.
-/
theorem imp_self (a : LetterlessFormula) : Provable (a ⇒ a) := by
  let h₁ : Provable (a ⇒ ((a ⇒ a) ⇒ a)) :=
    Provable.axiom1 a (a ⇒ a)
  let h₂ : Provable (a ⇒ (a ⇒ a)) :=
    Provable.axiom1 a a
  let h₃ :
      Provable ((a ⇒ ((a ⇒ a) ⇒ a)) ⇒ ((a ⇒ (a ⇒ a)) ⇒ (a ⇒ a))) :=
    Provable.axiom2 a (a ⇒ a) a
  exact Provable.modusPonens (Provable.modusPonens h₃ h₁) h₂

/--
Hypothetical syllogism inside the Hilbert system.
-/
theorem imp_trans {a b c : LetterlessFormula}
    (hab : Provable (a ⇒ b)) (hbc : Provable (b ⇒ c)) :
    Provable (a ⇒ c) := by
  let h₁ : Provable (a ⇒ (b ⇒ c)) := weaken (a := a) hbc
  let h₂ : Provable ((a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))) :=
    Provable.axiom2 a b c
  exact Provable.modusPonens (Provable.modusPonens h₂ h₁) hab

/--
Pointwise modus ponens under a shared antecedent.
-/
theorem imp_mp {a b c : LetterlessFormula}
    (hab : Provable (a ⇒ b)) (habc : Provable (a ⇒ (b ⇒ c))) :
    Provable (a ⇒ c) := by
  let h₂ : Provable ((a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))) :=
    Provable.axiom2 a b c
  exact Provable.modusPonens (Provable.modusPonens h₂ habc) hab

/--
Ex falso for the letterless fragment.
-/
theorem ex_falso (a : LetterlessFormula) : Provable (⊥ ⇒ a) := by
  let h₁ : Provable (⊥ ⇒ (((a ⇒ ⊥) ⇒ ⊥) ⇒ a)) :=
    weaken (a := ⊥) (Provable.axiomClassical a)
  let h₂ : Provable (⊥ ⇒ ((a ⇒ ⊥) ⇒ ⊥)) :=
    Provable.axiom1 ⊥ (a ⇒ ⊥)
  let h₃ :
      Provable ((⊥ ⇒ (((a ⇒ ⊥) ⇒ ⊥) ⇒ a)) ⇒
        ((⊥ ⇒ ((a ⇒ ⊥) ⇒ ⊥)) ⇒ (⊥ ⇒ a))) :=
    Provable.axiom2 ⊥ ((a ⇒ ⊥) ⇒ ⊥) a
  exact Provable.modusPonens (Provable.modusPonens h₃ h₁) h₂

/--
Monotonicity of `□` at the level of provability.
-/
theorem box_mono {a b : LetterlessFormula} (hab : Provable (a ⇒ b)) :
    Provable (□a ⇒ □b) :=
  Provable.modusPonens (Provable.axiomK a b) (Provable.necessitation hab)

/--
Derived composition inside the Hilbert system.
-/
theorem imp_compose (a b c : LetterlessFormula) :
    Provable ((b ⇒ c) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))) := by
  have h₁ : Provable ((b ⇒ c) ⇒ (a ⇒ (b ⇒ c))) :=
    Provable.axiom1 (b ⇒ c) a
  have h₂ : Provable ((a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))) :=
    Provable.axiom2 a b c
  exact imp_trans h₁ h₂

/--
If `⊢ a ⇒ b`, then `⊢ (b ⇒ c) ⇒ (a ⇒ c)`.
-/
theorem imp_postcompose {a b c : LetterlessFormula} (hab : Provable (a ⇒ b)) :
    Provable ((b ⇒ c) ⇒ (a ⇒ c)) := by
  have h₁ : Provable ((b ⇒ c) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))) :=
    imp_compose a b c
  have h₂ : Provable ((b ⇒ c) ⇒ (a ⇒ b)) :=
    weaken (a := (b ⇒ c)) hab
  have h₃ :
      Provable (((b ⇒ c) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))) ⇒
        (((b ⇒ c) ⇒ (a ⇒ b)) ⇒ ((b ⇒ c) ⇒ (a ⇒ c)))) :=
    Provable.axiom2 (b ⇒ c) (a ⇒ b) (a ⇒ c)
  exact Provable.modusPonens (Provable.modusPonens h₃ h₁) h₂

/--
Swap antecedents in a nested implication.
-/
theorem imp_swap (a b c : LetterlessFormula) :
    Provable ((a ⇒ (b ⇒ c)) ⇒ (b ⇒ (a ⇒ c))) := by
  let H := (a ⇒ (b ⇒ c))
  have hH : Provable (H ⇒ H) :=
    imp_self H
  have h₁ : Provable (H ⇒ ((a ⇒ b) ⇒ (a ⇒ c))) := by
    exact imp_mp hH (weaken (a := H) (Provable.axiom2 a b c))
  have h₂ : Provable (H ⇒ (b ⇒ (a ⇒ b))) :=
    weaken (a := H) (Provable.axiom1 b a)
  have h₃ :
      Provable (H ⇒ (((a ⇒ b) ⇒ (a ⇒ c)) ⇒ ((b ⇒ (a ⇒ b)) ⇒ (b ⇒ (a ⇒ c))))) :=
    weaken (a := H) (imp_compose b (a ⇒ b) (a ⇒ c))
  have h₄ : Provable (H ⇒ ((b ⇒ (a ⇒ b)) ⇒ (b ⇒ (a ⇒ c)))) :=
    imp_mp h₁ h₃
  exact imp_mp h₂ h₄

/--
Contravariance of negation at the level of provability.
-/
theorem neg_mono {a b : LetterlessFormula} (hab : Provable (a ⇒ b)) :
    Provable (LetterlessFormula.neg b ⇒ LetterlessFormula.neg a) := by
  simpa [LetterlessFormula.neg] using imp_postcompose (c := ⊥) hab

/--
Double-negation introduction.
-/
theorem doubleNeg_intro (a : LetterlessFormula) :
    Provable (a ⇒ LetterlessFormula.neg (LetterlessFormula.neg a)) := by
  have h₁ : Provable (((a ⇒ ⊥) ⇒ a) ⇒ ((a ⇒ ⊥) ⇒ ⊥)) := by
    have hbase : Provable (((a ⇒ ⊥) ⇒ (a ⇒ ⊥)) ⇒ (((a ⇒ ⊥) ⇒ a) ⇒ ((a ⇒ ⊥) ⇒ ⊥))) :=
      Provable.axiom2 (a ⇒ ⊥) a ⊥
    exact Provable.modusPonens hbase (imp_self (a ⇒ ⊥))
  have h₂ : Provable (a ⇒ ((a ⇒ ⊥) ⇒ a)) :=
    Provable.axiom1 a (a ⇒ ⊥)
  exact imp_trans h₂ h₁

/--
Double-negation elimination from the classical axiom.
-/
theorem doubleNeg_elim (a : LetterlessFormula) :
    Provable (LetterlessFormula.neg (LetterlessFormula.neg a) ⇒ a) :=
  Provable.axiomClassical a

/--
Classical equivalence between a formula and its double negation.
-/
theorem eqv_doubleNeg (a : LetterlessFormula) :
    Eqv a (LetterlessFormula.neg (LetterlessFormula.neg a)) :=
  ⟨doubleNeg_intro a, doubleNeg_elim a⟩

/--
Reflexivity of provable equivalence.
-/
theorem eqv_refl (a : LetterlessFormula) : Eqv a a :=
  ⟨imp_self a, imp_self a⟩

/--
Symmetry of provable equivalence.
-/
theorem eqv_symm {a b : LetterlessFormula} (h : Eqv a b) : Eqv b a :=
  ⟨h.2, h.1⟩

/--
Transitivity of provable equivalence.
-/
theorem eqv_trans {a b c : LetterlessFormula}
    (hab : Eqv a b) (hbc : Eqv b c) : Eqv a c :=
  ⟨imp_trans hab.1 hbc.1, imp_trans hbc.2 hab.2⟩

/--
Provable equivalence implies semantic equality.
-/
theorem eqv_sound {a b : LetterlessFormula} (h : Eqv a b) :
    LetterlessFormula.eval a = LetterlessFormula.eval b := by
  funext t
  have hab := provable_sound h.1
  have hba := provable_sound h.2
  have habt : LetterlessFormula.eval (a ⇒ b) t = true := by
    simpa [const1, const] using congrArg (fun f => f t) hab
  have hbat : LetterlessFormula.eval (b ⇒ a) t = true := by
    simpa [const1, const] using congrArg (fun f => f t) hba
  cases ha : LetterlessFormula.eval a t <;> cases hb : LetterlessFormula.eval b t <;>
    simp [LetterlessFormula.eval, bimplies, ha, hb] at habt hbat ⊢

/--
Provable equivalence is preserved by `□`.
-/
theorem eqv_box {a b : LetterlessFormula} (h : Eqv a b) :
    Eqv (□a) (□b) :=
  ⟨box_mono h.1, box_mono h.2⟩

/--
Provable equivalence is preserved by negation.
-/
theorem eqv_neg {a b : LetterlessFormula} (h : Eqv a b) :
    Eqv (LetterlessFormula.neg a) (LetterlessFormula.neg b) :=
  ⟨neg_mono h.2, neg_mono h.1⟩

/--
Classical equivalence between a formula and its fourfold negation.
-/
theorem eqv_fourNeg (a : LetterlessFormula) :
    Eqv a (LetterlessFormula.neg (LetterlessFormula.neg
      (LetterlessFormula.neg (LetterlessFormula.neg a)))) := by
  have h₁ : Eqv a (LetterlessFormula.neg (LetterlessFormula.neg a)) :=
    eqv_doubleNeg a
  have h₂ :
      Eqv (LetterlessFormula.neg (LetterlessFormula.neg a))
        (LetterlessFormula.neg (LetterlessFormula.neg
          (LetterlessFormula.neg (LetterlessFormula.neg a)))) :=
    eqv_neg (eqv_neg (eqv_doubleNeg a))
  exact eqv_trans h₁ h₂

/--
Provable equivalence is preserved by implication.
-/
theorem eqv_imp {a a' b b' : LetterlessFormula}
    (ha : Eqv a a') (hb : Eqv b b') :
    Eqv (a ⇒ b) (a' ⇒ b') := by
  constructor
  · have h₁ : Provable ((a ⇒ b) ⇒ (a' ⇒ b)) :=
      imp_postcompose (a := a') (b := a) (c := b) ha.2
    have h₂ : Provable ((a' ⇒ b) ⇒ (a' ⇒ b')) :=
      Provable.modusPonens (imp_compose a' b b') hb.1
    exact imp_trans h₁ h₂
  · have h₁ : Provable ((a' ⇒ b') ⇒ (a ⇒ b')) :=
      imp_postcompose (a := a) (b := a') (c := b') ha.1
    have h₂ : Provable ((a ⇒ b') ⇒ (a ⇒ b)) :=
      Provable.modusPonens (imp_compose a b' b) hb.2
    exact imp_trans h₁ h₂

end Provable

/-
This file begins a reconstruction, inside Lean, of the letterless completeness
argument from Boolos' Chapter 7, but phrased in the language of bitstreams
rather than traces whenever possible.

The immediate normal forms are built from the formulas `iterBoxBottom n`,
whose denotations are the initial segments `{ t | t < n }`. Boolos' key
observation is that every letterless denotation is finite or cofinite, and that
these two cases can be represented by finite Boolean combinations of such
initial-segment formulas.

What is proved here is the first proof-theoretic layer needed for that program:
the Hilbert system can derive the monotone chain

  ⊥ ⇒ □⊥ ⇒ □□⊥ ⇒ ...

corresponding semantically to the inclusions

  ∅ ⊆ {0} ⊆ {0,1} ⊆ ...
-/

/--
The basic step in the chain of initial-segment formulas.
-/
theorem provable_iterBoxBottom_step (n : Nat) :
    Provable (LetterlessFormula.iterBoxBottom n ⇒
      LetterlessFormula.iterBoxBottom (n + 1)) := by
  induction n with
  | zero =>
      simpa [LetterlessFormula.iterBoxBottom] using
        Provable.ex_falso (□⊥)
  | succ n ih =>
      simpa [LetterlessFormula.iterBoxBottom] using
        Provable.box_mono ih

/--
If `n ≤ m`, then `□^n ⊥ ⇒ □^m ⊥` is provable.
-/
theorem provable_iterBoxBottom_monotone {n m : Nat} (h : n ≤ m) :
    Provable (LetterlessFormula.iterBoxBottom n ⇒
      LetterlessFormula.iterBoxBottom m) := by
  induction h with
  | refl =>
      exact Provable.imp_self _
  | @step m h ih =>
      exact Provable.imp_trans ih (provable_iterBoxBottom_step m)

/--
Negated initial-segment formulas form the reverse implication chain.
-/
theorem provable_neg_iterBoxBottom_antitone {n m : Nat} (h : n ≤ m) :
    Provable (LetterlessFormula.neg (LetterlessFormula.iterBoxBottom m) ⇒
      LetterlessFormula.neg (LetterlessFormula.iterBoxBottom n)) := by
  exact Provable.neg_mono (provable_iterBoxBottom_monotone h)

/--
Boolos-style implication clause built from two initial-segment formulas.
-/
def iterClause (m n : Nat) : LetterlessFormula :=
  LetterlessFormula.iterBoxBottom m ⇒ LetterlessFormula.iterBoxBottom n

/--
If `m ≤ n`, the clause `□^m ⊥ ⇒ □^n ⊥` is provable.
-/
theorem provable_iterClause_of_le {m n : Nat} (h : m ≤ n) :
    Provable (iterClause m n) :=
  provable_iterBoxBottom_monotone h

/--
The formula `⊤` is provable.
-/
theorem provable_top : Provable LetterlessFormula.top := by
  simpa [LetterlessFormula.top] using Provable.imp_self ⊥

/--
Any provable formula is provably equivalent to `⊤`.
-/
theorem eqv_of_provable {a : LetterlessFormula} (ha : Provable a) :
    Provable.Eqv a LetterlessFormula.top := by
  constructor
  · exact Provable.weaken (a := a) provable_top
  · exact Provable.weaken (a := LetterlessFormula.top) ha

/--
`□⊤` is provably equivalent to `⊤`.
-/
theorem eqv_box_top :
    Provable.Eqv (□LetterlessFormula.top) LetterlessFormula.top :=
  eqv_of_provable (Provable.necessitation provable_top)

/--
Boxing an iterated bottom just advances the iteration.
-/
theorem eqv_box_iterBoxBottom (n : Nat) :
    Provable.Eqv (□(LetterlessFormula.iterBoxBottom n))
      (LetterlessFormula.iterBoxBottom (n + 1)) := by
  simpa [LetterlessFormula.iterBoxBottom] using
    (Provable.eqv_refl (□(LetterlessFormula.iterBoxBottom n)))

/--
If `m ≤ n`, the clause `□^m ⊥ ⇒ □^n ⊥` is provably equivalent to `⊤`.
-/
theorem eqv_iterClause_top_of_le {m n : Nat} (h : m ≤ n) :
    Provable.Eqv (iterClause m n) LetterlessFormula.top := by
  constructor
  · exact Provable.weaken (a := iterClause m n) provable_top
  · exact Provable.weaken (a := LetterlessFormula.top) (provable_iterClause_of_le h)

/--
Semantic description of a Boolos-style implication clause.
-/
theorem eval_iterClause (m n : Nat) :
    LetterlessFormula.eval (iterClause m n) =
      fun t => decide (m ≤ t ∨ t < n) := by
  funext t
  by_cases hm : t < m
  · by_cases hn : t < n
    · simp [iterClause, LetterlessFormula.eval_imp, LetterlessFormula.eval_iterBoxBottom,
        bimplies, hm, hn]
    · have hmtrue : decide (t < m) = true := by simp [hm]
      have hnfalse : decide (t < n) = false := by simp [hn]
      have hdisj : ¬ (m ≤ t ∨ t < n) := by
        intro h
        rcases h with hmt | htn
        · exact Nat.not_lt_of_ge hmt hm
        · exact hn htn
      simp [iterClause, LetterlessFormula.eval_imp, LetterlessFormula.eval_iterBoxBottom,
        bimplies, hmtrue, hnfalse, hdisj]
  · have hge : m ≤ t := Nat.le_of_not_gt hm
    by_cases hn : t < n
    · have hmfalse : decide (t < m) = false := by simp [hm]
      have hntrue : decide (t < n) = true := by simp [hn]
      simp [iterClause, LetterlessFormula.eval_imp, LetterlessFormula.eval_iterBoxBottom,
        bimplies, hmfalse, hntrue, hge]
    · have hmfalse : decide (t < m) = false := by simp [hm]
      have hnfalse : decide (t < n) = false := by simp [hn]
      simp [iterClause, LetterlessFormula.eval_imp, LetterlessFormula.eval_iterBoxBottom,
        bimplies, hmfalse, hnfalse, hge]

namespace LetterlessFormula

/--
Conjunction defined in the implication/`⊥` fragment.
-/
def conj (a b : LetterlessFormula) : LetterlessFormula :=
  neg (a ⇒ neg b)

infixr:61 " &&& " => conj

/--
Canonical normal form for a finite set of times.
-/
def finiteNormalForm : List Nat → LetterlessFormula
  | [] => ⊥
  | n :: ns => disj (pulseAt n) (finiteNormalForm ns)

/--
Canonical normal form for the cofinite set obtained by removing the listed
times.
-/
def cofiniteNormalForm (ns : List Nat) : LetterlessFormula :=
  neg (finiteNormalForm ns)

theorem eval_finiteNormalForm_true_iff (ns : List Nat) (t : Nat) :
    eval (finiteNormalForm ns) t = true ↔ t ∈ ns := by
  induction ns with
  | nil =>
      simp [finiteNormalForm, eval_bottom, const0, const]
  | cons n ns ih =>
      rw [finiteNormalForm, eval_disj]
      constructor
      · intro h
        by_cases hp : eval (pulseAt n) t = true
        · have hEq : t = n := (eval_pulseAt_true_iff n t).mp hp
          simp [hEq]
        · have hrest : eval (finiteNormalForm ns) t = true := by
            cases hq : eval (finiteNormalForm ns) t with
            | false =>
                simp [bor, hp, hq] at h
            | true =>
                simp
          exact List.mem_cons_of_mem _ (ih.mp hrest)
      · intro h
        rcases List.mem_cons.mp h with rfl | hmem
        · rw [eval_pulseAt]
          simp [bor]
        · have hrest : eval (finiteNormalForm ns) t = true := ih.mpr hmem
          cases hp : eval (pulseAt n) t <;> simp [bor, hp, hrest]

theorem eval_finiteNormalForm (ns : List Nat) :
    eval (finiteNormalForm ns) = fun t => decide (t ∈ ns) := by
  funext t
  by_cases hmem : t ∈ ns
  · have htrue : eval (finiteNormalForm ns) t = true :=
      (eval_finiteNormalForm_true_iff ns t).mpr hmem
    simp [htrue, hmem]
  · have hfalse : eval (finiteNormalForm ns) t = false := by
      cases hval : eval (finiteNormalForm ns) t with
      | false =>
          exact rfl
      | true =>
          exact False.elim (hmem ((eval_finiteNormalForm_true_iff ns t).mp hval))
    simp [hfalse, hmem]

theorem eval_cofiniteNormalForm_true_iff (ns : List Nat) (t : Nat) :
    eval (cofiniteNormalForm ns) t = true ↔ t ∉ ns := by
  rw [cofiniteNormalForm, eval_neg]
  constructor
  · intro h
    cases hfin : eval (finiteNormalForm ns) t with
    | false =>
        intro hmem
        have : eval (finiteNormalForm ns) t = true :=
          (eval_finiteNormalForm_true_iff ns t).mpr hmem
        simp [hfin] at this
    | true =>
        have : t ∈ ns := (eval_finiteNormalForm_true_iff ns t).mp hfin
        have hcontra : False := by
          simp [bnot, hfin] at h
        exact False.elim hcontra
  · intro hnot
    have hfalse : eval (finiteNormalForm ns) t = false := by
      cases hval : eval (finiteNormalForm ns) t with
      | false =>
          exact rfl
      | true =>
          exact False.elim (hnot ((eval_finiteNormalForm_true_iff ns t).mp hval))
    simp [hfalse, bnot]

theorem eval_cofiniteNormalForm (ns : List Nat) :
    eval (cofiniteNormalForm ns) = fun t => decide (t ∉ ns) := by
  funext t
  by_cases hmem : t ∈ ns
  · have hfalse : eval (cofiniteNormalForm ns) t = false := by
      cases hval : eval (cofiniteNormalForm ns) t with
      | false =>
          exact rfl
      | true =>
          exact False.elim (((eval_cofiniteNormalForm_true_iff ns t).mp hval) hmem)
    simp [hfalse, hmem]
  · have htrue : eval (cofiniteNormalForm ns) t = true :=
      (eval_cofiniteNormalForm_true_iff ns t).mpr hmem
    simp [htrue, hmem]

theorem eval_conj (a b : LetterlessFormula) :
    eval (a &&& b) = eval a &&& eval b := by
  funext t
  cases ha : eval a t <;> cases hb : eval b t <;>
    simp [conj, neg, eval, bimplies, band, const0, const, ha, hb]

/--
The finite interval `[n, m)` viewed as the gap in the clause `□^m ⊥ ⇒ □^n ⊥`.
-/
def clauseGap (m n : Nat) : List Nat :=
  (List.range m).filter fun t => n ≤ t

theorem mem_clauseGap_iff (m n t : Nat) :
    t ∈ clauseGap m n ↔ n ≤ t ∧ t < m := by
  constructor
  · intro h
    simp [clauseGap] at h
    exact ⟨h.2, h.1⟩
  · intro h
    simp [clauseGap, h.2, h.1]

/--
Semantically, every Boolos-style implication clause is a cofinite normal form
whose finite set of false times is exactly the interval `[n,m)`.
-/
theorem eval_iterClause_as_cofiniteNormalForm (m n : Nat) :
    eval (iterClause m n) = eval (cofiniteNormalForm (clauseGap m n)) := by
  funext t
  rw [eval_iterClause, eval_cofiniteNormalForm]
  by_cases htrue : m ≤ t ∨ t < n
  · have hnotmem : t ∉ clauseGap m n := by
      intro hmem
      have hgap : n ≤ t ∧ t < m := (mem_clauseGap_iff m n t).mp hmem
      rcases htrue with hmt | htn
      · exact Nat.not_lt_of_ge hmt hgap.2
      · exact Nat.not_le_of_gt htn hgap.1
    simp [htrue, hnotmem]
  · have hmem : t ∈ clauseGap m n := by
      apply (mem_clauseGap_iff m n t).2
      constructor
      · exact Nat.le_of_not_gt (fun htn => htrue (Or.inr htn))
      · exact Nat.lt_of_not_ge (fun hmt => htrue (Or.inl hmt))
    simp [htrue, hmem]

theorem eval_conj_cofiniteNormalForm (ns ms : List Nat) :
    eval (cofiniteNormalForm ns &&& cofiniteNormalForm ms) =
      eval (cofiniteNormalForm (ns ++ ms)) := by
  funext t
  rw [eval_conj, eval_cofiniteNormalForm, eval_cofiniteNormalForm, eval_cofiniteNormalForm]
  by_cases hn : t ∈ ns
  · have happ : t ∈ ns ++ ms := List.mem_append.mpr (Or.inl hn)
    simp [band, hn, happ]
  · by_cases hm : t ∈ ms
    · have happ : t ∈ ns ++ ms := List.mem_append.mpr (Or.inr hm)
      simp [band, hn, hm, happ]
    · have happ : t ∉ ns ++ ms := by
        intro h
        rcases List.mem_append.mp h with hns | hms
        · exact hn hns
        · exact hm hms
      simp [band, hn, hm, happ]

/--
An adjacent clause `□^(n+1)⊥ ⇒ □^n⊥` is semantically the same as a
single-hole cofinite normal form.
-/
theorem eval_adjacentClause_singleHole (n : Nat) :
    eval (iterClause (n + 1) n) = eval (cofiniteNormalForm [n]) := by
  funext t
  rw [eval_iterClause, eval_cofiniteNormalForm]
  by_cases hlt : t < n
  · have hnot : t ∉ [n] := by simp [Nat.ne_of_lt hlt]
    simp [hlt, hnot]
  · by_cases heq : t = n
    · subst t
      simp
    · have hge : n + 1 ≤ t := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq))
      have hnot : t ∉ [n] := by simp [heq]
      simp [hlt, hge, hnot]

/--
A conjunction of single-hole cofinite normal forms.
-/
def holeConjunction : List Nat → LetterlessFormula
  | [] => top
  | n :: ns => conj (cofiniteNormalForm [n]) (holeConjunction ns)

/--
Recursive conjunction of single-hole normal forms indexed by gap length.
-/
def holeSpan : Nat → Nat → LetterlessFormula
  | _, 0 => top
  | n, k + 1 => conj (cofiniteNormalForm [n]) (holeSpan (n + 1) k)

theorem eval_holeConjunction (ns : List Nat) :
    eval (holeConjunction ns) = eval (cofiniteNormalForm ns) := by
  induction ns with
  | nil =>
      rfl
  | cons n ns ih =>
      calc
        eval (holeConjunction (n :: ns))
            = eval (cofiniteNormalForm [n]) &&& eval (holeConjunction ns) := by
                rw [holeConjunction, eval_conj]
        _ = eval (cofiniteNormalForm [n]) &&& eval (cofiniteNormalForm ns) := by
                rw [ih]
        _ = eval (cofiniteNormalForm [n] &&& cofiniteNormalForm ns) := by
                symm
                exact eval_conj (cofiniteNormalForm [n]) (cofiniteNormalForm ns)
        _ = eval (cofiniteNormalForm (n :: ns)) := by
                simpa using eval_conj_cofiniteNormalForm [n] ns

theorem eval_holeSpan (n k : Nat) :
    eval (holeSpan n k) =
      eval (holeConjunction (List.range' n k)) := by
  induction k generalizing n with
  | zero =>
      rfl
  | succ k ih =>
      calc
        eval (holeSpan n (k + 1))
            = eval (cofiniteNormalForm [n]) &&& eval (holeSpan (n + 1) k) := by
                rw [holeSpan, eval_conj]
        _ = eval (cofiniteNormalForm [n]) &&&
              eval (holeConjunction (List.range' (n + 1) k)) := by
                rw [ih]
        _ = eval (conj (cofiniteNormalForm [n]) (holeConjunction (List.range' (n + 1) k))) := by
                symm
                exact eval_conj (cofiniteNormalForm [n]) (holeConjunction (List.range' (n + 1) k))
        _ = eval (holeConjunction (List.range' n (k + 1))) := by
                rw [List.range'_succ, holeConjunction]

/--
The adjacent clause at time `n`.
-/
def adjacentClause (n : Nat) : LetterlessFormula :=
  iterClause (n + 1) n

/--
Conjunction of adjacent clauses over a list of hole positions.
-/
def adjacentClauseConjunction : List Nat → LetterlessFormula
  | [] => top
  | n :: ns => conj (adjacentClause n) (adjacentClauseConjunction ns)

/--
Recursive adjacent-clause conjunction indexed by gap length.
-/
def adjacentSpan : Nat → Nat → LetterlessFormula
  | _, 0 => top
  | n, k + 1 => conj (adjacentClause n) (adjacentSpan (n + 1) k)

theorem eval_adjacentClauseConjunction (ns : List Nat) :
    eval (adjacentClauseConjunction ns) = eval (holeConjunction ns) := by
  induction ns with
  | nil =>
      rfl
  | cons n ns ih =>
      rw [adjacentClauseConjunction, holeConjunction, eval_conj, eval_conj, ih, adjacentClause,
        eval_adjacentClause_singleHole]

theorem eval_adjacentSpan (n k : Nat) :
    eval (adjacentSpan n k) =
      eval (adjacentClauseConjunction (List.range' n k)) := by
  induction k generalizing n with
  | zero =>
      rfl
  | succ k ih =>
      calc
        eval (adjacentSpan n (k + 1))
            = eval (adjacentClause n) &&& eval (adjacentSpan (n + 1) k) := by
                rw [adjacentSpan, eval_conj]
        _ = eval (adjacentClause n) &&&
              eval (adjacentClauseConjunction (List.range' (n + 1) k)) := by
                rw [ih]
        _ = eval (conj (adjacentClause n) (adjacentClauseConjunction (List.range' (n + 1) k))) := by
                symm
                exact eval_conj (adjacentClause n) (adjacentClauseConjunction (List.range' (n + 1) k))
        _ = eval (adjacentClauseConjunction (List.range' n (k + 1))) := by
                rw [List.range'_succ, adjacentClauseConjunction]

theorem mem_range'_iff (n k t : Nat) :
    t ∈ List.range' n k ↔ n ≤ t ∧ t < n + k := by
  constructor
  · intro h
    rcases List.mem_range'.mp h with ⟨i, hi, rfl⟩
    constructor
    · simp
    · simpa using Nat.add_lt_add_left hi n
  · intro h
    refine List.mem_range'.mpr ?_
    refine ⟨t - n, ?_, ?_⟩
    · have hlt : n + (t - n) < n + k := by
        simpa [Nat.add_sub_of_le h.1] using h.2
      simpa using hlt
    · simpa [Nat.mul_one] using (Nat.add_sub_of_le h.1).symm

/--
Semantically, the recursive single-hole span from `n` of length `k` is exactly
the long clause `□^(n+k)⊥ ⇒ □^n⊥`.
-/
theorem eval_iterClause_as_holeSpan (n k : Nat) :
    eval (iterClause (n + k) n) = eval (holeSpan n k) := by
  calc
    eval (iterClause (n + k) n)
        = eval (cofiniteNormalForm (List.range' n k)) := by
            funext t
            rw [eval_iterClause, eval_cofiniteNormalForm]
            by_cases htrue : n + k ≤ t ∨ t < n
            · have hnotmem : t ∉ List.range' n k := by
                intro hmem
                have hmem' : n ≤ t ∧ t < n + k := (mem_range'_iff n k t).mp hmem
                rcases htrue with hge | hlt
                · exact Nat.not_lt_of_ge hge hmem'.2
                · exact Nat.not_le_of_gt hlt hmem'.1
              simp [htrue, hnotmem]
            · have hmem : t ∈ List.range' n k := by
                apply (mem_range'_iff n k t).2
                constructor
                · exact Nat.le_of_not_gt (fun hlt => htrue (Or.inr hlt))
                · exact Nat.lt_of_not_ge (fun hge => htrue (Or.inl hge))
              simp [htrue, hmem]
    _ = eval (holeConjunction (List.range' n k)) := by
          symm
          exact eval_holeConjunction (List.range' n k)
    _ = eval (holeSpan n k) := by
          symm
          exact eval_holeSpan n k

theorem clauseGap_eq_range' {m n : Nat} (h : n ≤ m) :
    clauseGap m n = List.range' n (m - n) := by
  rw [clauseGap, List.range_eq_range']
  have happ : List.range' 0 n ++ List.range' n (m - n) = List.range' 0 m := by
    simpa [Nat.add_sub_of_le h] using (List.range'_append_1 (s := 0) (m := n) (n := m - n))
  rw [← happ, List.filter_append]
  have hnil : List.filter (fun t => decide (n ≤ t)) (List.range' 0 n) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    rcases List.mem_range'.mp ht with ⟨i, hi, hti⟩
    have htlt : t < n := by simpa [hti] using hi
    simp [Nat.not_le_of_gt htlt]
  have hself : List.filter (fun t => decide (n ≤ t)) (List.range' n (m - n)) = List.range' n (m - n) := by
    apply (List.filter_eq_self).2
    intro t ht
    rcases List.mem_range'.mp ht with ⟨i, hi, hti⟩
    simp [hti]
  simp [hnil, hself]

/--
The list of adjacent one-hole positions making up the gap `[n,m)`.
-/
def clauseHoleList (m n : Nat) : List Nat :=
  (List.range m).filter fun t => n ≤ t

theorem clauseHoleList_eq_clauseGap (m n : Nat) :
    clauseHoleList m n = clauseGap m n := rfl

/--
Semantically, the nontrivial clause `□^m⊥ ⇒ □^n⊥` is the conjunction of the
adjacent single-hole clauses for each missing time in `[n,m)`.
-/
theorem eval_iterClause_as_holeConjunction (m n : Nat) :
    eval (iterClause m n) = eval (holeConjunction (clauseHoleList m n)) := by
  calc
    eval (iterClause m n) = eval (cofiniteNormalForm (clauseGap m n)) := by
      exact eval_iterClause_as_cofiniteNormalForm m n
    _ = eval (cofiniteNormalForm (clauseHoleList m n)) := by
      simp [clauseHoleList_eq_clauseGap]
    _ = eval (holeConjunction (clauseHoleList m n)) := by
      symm
      exact eval_holeConjunction (clauseHoleList m n)

/--
A general clause is semantically the conjunction of the adjacent clauses
corresponding to each missing time in its finite gap.
-/
theorem eval_iterClause_as_adjacentClauseConjunction (m n : Nat) :
    eval (iterClause m n) =
      eval (adjacentClauseConjunction (clauseHoleList m n)) := by
  calc
    eval (iterClause m n) = eval (holeConjunction (clauseHoleList m n)) := by
      exact eval_iterClause_as_holeConjunction m n
    _ = eval (adjacentClauseConjunction (clauseHoleList m n)) := by
      symm
      exact eval_adjacentClauseConjunction (clauseHoleList m n)

end LetterlessFormula

namespace Provable

/--
Provable equivalence is preserved by the derived conjunction.
-/
theorem eqv_conj {a a' b b' : LetterlessFormula}
    (ha : Eqv a a') (hb : Eqv b b') :
    Eqv (LetterlessFormula.conj a b) (LetterlessFormula.conj a' b') := by
  simp [LetterlessFormula.conj]
  exact eqv_neg (eqv_imp ha (eqv_neg hb))

/--
Provable equivalence is preserved by the derived disjunction.
-/
theorem eqv_disj {a a' b b' : LetterlessFormula}
    (ha : Eqv a a') (hb : Eqv b b') :
    Eqv (LetterlessFormula.disj a b) (LetterlessFormula.disj a' b') := by
  simp [LetterlessFormula.disj]
  exact eqv_imp (eqv_neg ha) hb

/--
Elimination of the left conjunct for the derived conjunction.
-/
theorem conj_elim_left (a b : LetterlessFormula) :
    Provable (LetterlessFormula.conj a b ⇒ a) := by
  have h₁ : Provable (LetterlessFormula.neg a ⇒ (a ⇒ LetterlessFormula.neg b)) := by
    have hbase : Provable (⊥ ⇒ LetterlessFormula.neg b) :=
      ex_falso (LetterlessFormula.neg b)
    have hcomp :
        Provable ((⊥ ⇒ LetterlessFormula.neg b) ⇒
          ((a ⇒ ⊥) ⇒ (a ⇒ LetterlessFormula.neg b))) :=
      imp_compose a ⊥ (LetterlessFormula.neg b)
    simpa [LetterlessFormula.neg] using Provable.modusPonens hcomp hbase
  have h₂ : Provable (LetterlessFormula.conj a b ⇒ LetterlessFormula.neg (LetterlessFormula.neg a)) := by
    simpa [LetterlessFormula.conj] using neg_mono h₁
  exact imp_trans h₂ (doubleNeg_elim a)

/--
Elimination of the right conjunct for the derived conjunction.
-/
theorem conj_elim_right (a b : LetterlessFormula) :
    Provable (LetterlessFormula.conj a b ⇒ b) := by
  have h₁ : Provable (LetterlessFormula.neg b ⇒ (a ⇒ LetterlessFormula.neg b)) := by
    simpa [LetterlessFormula.neg] using Provable.axiom1 (LetterlessFormula.neg b) a
  have h₂ : Provable (LetterlessFormula.conj a b ⇒ LetterlessFormula.neg (LetterlessFormula.neg b)) := by
    simpa [LetterlessFormula.conj] using neg_mono h₁
  exact imp_trans h₂ (doubleNeg_elim b)

/--
Direct introduction of the derived conjunction.
-/
theorem conj_intro (a b c : LetterlessFormula) :
    Provable (a ⇒ b) → Provable (a ⇒ c) → Provable (a ⇒ LetterlessFormula.conj b c) := by
  intro hab hac
  have hbneg' : Provable (b ⇒ ((b ⇒ LetterlessFormula.neg c) ⇒ LetterlessFormula.neg c)) := by
    exact Provable.modusPonens
      (imp_swap (b ⇒ LetterlessFormula.neg c) b (LetterlessFormula.neg c))
      (imp_self (b ⇒ LetterlessFormula.neg c))
  have hswap :
      Provable (((b ⇒ LetterlessFormula.neg c) ⇒ (c ⇒ ⊥)) ⇒
        (c ⇒ ((b ⇒ LetterlessFormula.neg c) ⇒ ⊥))) :=
    imp_swap (b ⇒ LetterlessFormula.neg c) c ⊥
  have hb_to_ccontra :
      Provable (b ⇒ (c ⇒ ((b ⇒ LetterlessFormula.neg c) ⇒ ⊥))) := by
    have h₁ : Provable (b ⇒ (((b ⇒ LetterlessFormula.neg c) ⇒ (c ⇒ ⊥)) ⇒
          (c ⇒ ((b ⇒ LetterlessFormula.neg c) ⇒ ⊥)))) :=
      weaken (a := b) hswap
    have h₂ : Provable (b ⇒ ((b ⇒ LetterlessFormula.neg c) ⇒ (c ⇒ ⊥))) := by
      simpa [LetterlessFormula.neg] using hbneg'
    exact imp_mp h₂ h₁
  have h₃ : Provable (a ⇒ (b ⇒ (c ⇒ LetterlessFormula.conj b c))) := by
    simpa [LetterlessFormula.conj, LetterlessFormula.neg] using weaken (a := a) hb_to_ccontra
  have h₄ : Provable (a ⇒ (c ⇒ LetterlessFormula.conj b c)) := imp_mp hab h₃
  exact imp_mp hac h₄

/--
Associativity of the derived conjunction.
-/
theorem eqv_conj_assoc (a b c : LetterlessFormula) :
    Eqv (LetterlessFormula.conj (LetterlessFormula.conj a b) c)
      (LetterlessFormula.conj a (LetterlessFormula.conj b c)) := by
  constructor
  · have hca : Provable (LetterlessFormula.conj (LetterlessFormula.conj a b) c ⇒ a) := by
      exact imp_trans
        (conj_elim_left (LetterlessFormula.conj a b) c)
        (conj_elim_left a b)
    have hcb : Provable (LetterlessFormula.conj (LetterlessFormula.conj a b) c ⇒ b) := by
      exact imp_trans
        (conj_elim_left (LetterlessFormula.conj a b) c)
        (conj_elim_right a b)
    have hcc : Provable (LetterlessFormula.conj (LetterlessFormula.conj a b) c ⇒ c) := by
      exact conj_elim_right (LetterlessFormula.conj a b) c
    have hbc :
        Provable (LetterlessFormula.conj (LetterlessFormula.conj a b) c ⇒
          LetterlessFormula.conj b c) :=
      conj_intro _ _ _ hcb hcc
    exact conj_intro _ _ _ hca hbc
  · have hca : Provable (LetterlessFormula.conj a (LetterlessFormula.conj b c) ⇒ a) := by
      exact conj_elim_left a (LetterlessFormula.conj b c)
    have hcb : Provable (LetterlessFormula.conj a (LetterlessFormula.conj b c) ⇒ b) := by
      exact imp_trans
        (conj_elim_right a (LetterlessFormula.conj b c))
        (conj_elim_left b c)
    have hcc : Provable (LetterlessFormula.conj a (LetterlessFormula.conj b c) ⇒ c) := by
      exact imp_trans
        (conj_elim_right a (LetterlessFormula.conj b c))
        (conj_elim_right b c)
    have hab :
        Provable (LetterlessFormula.conj a (LetterlessFormula.conj b c) ⇒
          LetterlessFormula.conj a b) :=
      conj_intro _ _ _ hca hcb
    exact conj_intro _ _ _ hab hcc

/--
Idempotence of the derived conjunction.
-/
theorem eqv_conj_idem (a : LetterlessFormula) :
    Eqv (LetterlessFormula.conj a a) a := by
  constructor
  · exact conj_elim_left a a
  · exact conj_intro _ _ _ (Provable.imp_self a) (Provable.imp_self a)

/--
`a ∨ ⊥` is provably equivalent to `a`.
-/
theorem eqv_disj_bottom (a : LetterlessFormula) :
    Eqv (LetterlessFormula.disj a ⊥) a := by
  simpa [LetterlessFormula.disj, LetterlessFormula.neg] using eqv_symm (eqv_doubleNeg a)

/--
`⊥ ∨ a` is provably equivalent to `a`.
-/
theorem eqv_bottom_disj (a : LetterlessFormula) :
    Eqv (LetterlessFormula.disj ⊥ a) a := by
  constructor
  · have hself : Provable ((LetterlessFormula.top ⇒ a) ⇒ (LetterlessFormula.top ⇒ a)) :=
      imp_self (LetterlessFormula.top ⇒ a)
    have htop : Provable ((LetterlessFormula.top ⇒ a) ⇒ LetterlessFormula.top) :=
      weaken (a := (LetterlessFormula.top ⇒ a)) provable_top
    have hax :
        Provable (((LetterlessFormula.top ⇒ a) ⇒ (LetterlessFormula.top ⇒ a)) ⇒
          (((LetterlessFormula.top ⇒ a) ⇒ LetterlessFormula.top) ⇒
            ((LetterlessFormula.top ⇒ a) ⇒ a))) :=
      Provable.axiom2 (LetterlessFormula.top ⇒ a) LetterlessFormula.top a
    exact Provable.modusPonens (Provable.modusPonens hax hself) htop
  · simpa [LetterlessFormula.disj, LetterlessFormula.neg, LetterlessFormula.top] using
      (Provable.axiom1 a LetterlessFormula.top)

/--
Commutativity of the derived conjunction.
-/
theorem eqv_conj_comm (a b : LetterlessFormula) :
    Eqv (LetterlessFormula.conj a b) (LetterlessFormula.conj b a) := by
  constructor
  · exact conj_intro _ _ _ (conj_elim_right a b) (conj_elim_left a b)
  · exact conj_intro _ _ _ (conj_elim_right b a) (conj_elim_left b a)

/--
De Morgan equivalence for conjunction of negations.
-/
theorem eqv_conj_neg_neg (a b : LetterlessFormula) :
    Eqv (LetterlessFormula.conj (LetterlessFormula.neg a) (LetterlessFormula.neg b))
      (LetterlessFormula.neg (LetterlessFormula.disj a b)) := by
  simp [LetterlessFormula.conj, LetterlessFormula.disj, LetterlessFormula.neg]
  exact eqv_neg (eqv_imp (eqv_refl _) (eqv_symm (eqv_doubleNeg b)))

/--
De Morgan form of disjunction.
-/
theorem eqv_disj_as_neg_conj_neg (a b : LetterlessFormula) :
    Eqv (LetterlessFormula.disj a b)
      (LetterlessFormula.neg (LetterlessFormula.conj (LetterlessFormula.neg a) (LetterlessFormula.neg b))) := by
  exact eqv_symm <| eqv_trans
    (eqv_neg (eqv_conj_neg_neg a b))
    (eqv_symm (eqv_doubleNeg (LetterlessFormula.disj a b)))

/--
Associativity of the derived disjunction.
-/
theorem eqv_disj_assoc (a b c : LetterlessFormula) :
    Eqv (LetterlessFormula.disj (LetterlessFormula.disj a b) c)
      (LetterlessFormula.disj a (LetterlessFormula.disj b c)) := by
  have h₁ :
      Eqv (LetterlessFormula.disj (LetterlessFormula.disj a b) c)
        (LetterlessFormula.neg
          (LetterlessFormula.conj
            (LetterlessFormula.neg (LetterlessFormula.disj a b))
            (LetterlessFormula.neg c))) :=
    eqv_disj_as_neg_conj_neg (LetterlessFormula.disj a b) c
  have h₂ :
      Eqv (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.neg (LetterlessFormula.disj a b))
              (LetterlessFormula.neg c)))
          (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.conj (LetterlessFormula.neg a) (LetterlessFormula.neg b))
              (LetterlessFormula.neg c))) := by
    exact eqv_neg (eqv_conj (eqv_symm (eqv_conj_neg_neg a b)) (eqv_refl _))
  have h₃ :
      Eqv (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.conj (LetterlessFormula.neg a) (LetterlessFormula.neg b))
              (LetterlessFormula.neg c)))
          (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.neg a)
              (LetterlessFormula.conj (LetterlessFormula.neg b) (LetterlessFormula.neg c)))) := by
    exact eqv_neg (eqv_conj_assoc (LetterlessFormula.neg a) (LetterlessFormula.neg b) (LetterlessFormula.neg c))
  have h₄ :
      Eqv (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.neg a)
              (LetterlessFormula.conj (LetterlessFormula.neg b) (LetterlessFormula.neg c))))
          (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.neg a)
              (LetterlessFormula.neg (LetterlessFormula.disj b c)))) := by
    exact eqv_neg (eqv_conj (eqv_refl _) (eqv_conj_neg_neg b c))
  have h₅ :
      Eqv (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.neg a)
              (LetterlessFormula.neg (LetterlessFormula.disj b c))))
          (LetterlessFormula.disj a (LetterlessFormula.disj b c)) :=
    eqv_symm (eqv_disj_as_neg_conj_neg a (LetterlessFormula.disj b c))
  exact eqv_trans (eqv_trans (eqv_trans (eqv_trans h₁ h₂) h₃) h₄) h₅

/--
Idempotence of the derived disjunction.
-/
theorem eqv_disj_idem (a : LetterlessFormula) :
    Eqv (LetterlessFormula.disj a a) a := by
  have h₁ :
      Eqv (LetterlessFormula.disj a a)
        (LetterlessFormula.neg
          (LetterlessFormula.conj (LetterlessFormula.neg a) (LetterlessFormula.neg a))) :=
    eqv_disj_as_neg_conj_neg a a
  have h₂ :
      Eqv (LetterlessFormula.neg
          (LetterlessFormula.conj (LetterlessFormula.neg a) (LetterlessFormula.neg a)))
        (LetterlessFormula.neg (LetterlessFormula.neg a)) :=
    eqv_neg (eqv_conj_idem (LetterlessFormula.neg a))
  have h₃ : Eqv (LetterlessFormula.neg (LetterlessFormula.neg a)) a :=
    eqv_symm (eqv_doubleNeg a)
  exact eqv_trans h₁ (eqv_trans h₂ h₃)

/--
Commutativity of the derived disjunction.
-/
theorem eqv_disj_comm (a b : LetterlessFormula) :
    Eqv (LetterlessFormula.disj a b) (LetterlessFormula.disj b a) := by
  have h₁ :
      Eqv (LetterlessFormula.disj a b)
        (LetterlessFormula.neg
          (LetterlessFormula.conj (LetterlessFormula.neg a) (LetterlessFormula.neg b))) :=
    eqv_disj_as_neg_conj_neg a b
  have h₂ :
      Eqv
        (LetterlessFormula.neg
          (LetterlessFormula.conj (LetterlessFormula.neg a) (LetterlessFormula.neg b)))
        (LetterlessFormula.neg
          (LetterlessFormula.conj (LetterlessFormula.neg b) (LetterlessFormula.neg a))) :=
    eqv_neg (eqv_conj_comm _ _)
  have h₃ :
      Eqv
        (LetterlessFormula.neg
          (LetterlessFormula.conj (LetterlessFormula.neg b) (LetterlessFormula.neg a)))
        (LetterlessFormula.disj b a) :=
    eqv_symm (eqv_disj_as_neg_conj_neg b a)
  exact eqv_trans h₁ (eqv_trans h₂ h₃)

/--
Classical contraposition.
-/
theorem eqv_contrapositive (a b : LetterlessFormula) :
    Eqv ((LetterlessFormula.neg a) ⇒ (LetterlessFormula.neg b)) (b ⇒ a) := by
  have h₁ :
      Eqv ((LetterlessFormula.neg a) ⇒ (LetterlessFormula.neg b))
        (LetterlessFormula.disj a (LetterlessFormula.neg b)) := by
    simpa [LetterlessFormula.disj, LetterlessFormula.neg] using
      (Provable.eqv_refl ((LetterlessFormula.neg a) ⇒ (LetterlessFormula.neg b)))
  have h₂ :
      Eqv (LetterlessFormula.disj a (LetterlessFormula.neg b))
        (LetterlessFormula.disj (LetterlessFormula.neg b) a) :=
    eqv_disj_comm a (LetterlessFormula.neg b)
  have h₃ :
      Eqv (LetterlessFormula.disj (LetterlessFormula.neg b) a) (b ⇒ a) := by
    simpa [LetterlessFormula.disj, LetterlessFormula.neg] using
      (Provable.eqv_symm (Provable.eqv_imp (Provable.eqv_doubleNeg b) (Provable.eqv_refl a)))
  exact eqv_trans h₁ (eqv_trans h₂ h₃)

/--
Left introduction for the derived disjunction.
-/
theorem disj_intro_left (a b : LetterlessFormula) :
    Provable (a ⇒ LetterlessFormula.disj a b) := by
  have h₁ : Provable (a ⇒ LetterlessFormula.neg (LetterlessFormula.neg a)) :=
    Provable.doubleNeg_intro a
  have h₂ : Provable (LetterlessFormula.neg (LetterlessFormula.neg a) ⇒ LetterlessFormula.disj a b) := by
    have hbase : Provable (⊥ ⇒ b) := Provable.ex_falso b
    have hcomp :
        Provable ((⊥ ⇒ b) ⇒
          ((LetterlessFormula.neg a ⇒ ⊥) ⇒ (LetterlessFormula.neg a ⇒ b))) :=
      Provable.imp_compose (LetterlessFormula.neg a) ⊥ b
    exact Provable.modusPonens hcomp hbase
  exact Provable.imp_trans h₁ (by simpa [LetterlessFormula.disj, LetterlessFormula.neg] using h₂)

/--
Right introduction for the derived disjunction.
-/
theorem disj_intro_right (a b : LetterlessFormula) :
    Provable (b ⇒ LetterlessFormula.disj a b) := by
  simpa [LetterlessFormula.disj, LetterlessFormula.neg] using
    (Provable.axiom1 b (LetterlessFormula.neg a))

/--
Elimination for the derived disjunction.
-/
theorem disj_elim {a b c : LetterlessFormula}
    (hac : Provable (a ⇒ c)) (hbc : Provable (b ⇒ c)) :
    Provable (LetterlessFormula.disj a b ⇒ c) := by
  have hna : Provable (LetterlessFormula.neg c ⇒ LetterlessFormula.neg a) :=
    Provable.modusPonens (eqv_contrapositive c a).2 hac
  have hnb : Provable (LetterlessFormula.neg c ⇒ LetterlessFormula.neg b) :=
    Provable.modusPonens (eqv_contrapositive c b).2 hbc
  let d := LetterlessFormula.disj a b
  have hd : Provable (d ⇒ (LetterlessFormula.neg a ⇒ b)) := by
    simpa [d, LetterlessFormula.disj] using Provable.imp_self d
  have hna' : Provable (d ⇒ (LetterlessFormula.neg c ⇒ LetterlessFormula.neg a)) :=
    Provable.weaken (a := d) hna
  have hnb' : Provable (d ⇒ (LetterlessFormula.neg c ⇒ LetterlessFormula.neg b)) :=
    Provable.weaken (a := d) hnb
  have hstep₁ :
      Provable
        (d ⇒ ((LetterlessFormula.neg c ⇒ LetterlessFormula.neg a) ⇒
          (LetterlessFormula.neg c ⇒ b))) := by
    exact Provable.imp_mp hd <|
      Provable.weaken (a := d)
        (Provable.imp_compose (LetterlessFormula.neg c) (LetterlessFormula.neg a) b)
  have hpos : Provable (d ⇒ (LetterlessFormula.neg c ⇒ b)) :=
    Provable.imp_mp hna' hstep₁
  have hstep₂ :
      Provable
        (d ⇒ ((LetterlessFormula.neg c ⇒ b) ⇒
          (LetterlessFormula.neg c ⇒ ⊥))) := by
    exact Provable.imp_mp hnb' <|
      Provable.weaken (a := d)
        (Provable.axiom2 (LetterlessFormula.neg c) b ⊥)
  have hcontra : Provable (d ⇒ (LetterlessFormula.neg c ⇒ ⊥)) :=
    Provable.imp_mp hpos hstep₂
  have hclass : Provable (d ⇒ ((LetterlessFormula.neg c ⇒ ⊥) ⇒ c)) :=
    Provable.weaken (a := d) (Provable.axiomClassical c)
  exact Provable.imp_mp hcontra hclass

/--
Curried introduction of the derived conjunction.
-/
theorem conj_intro_curried (a b : LetterlessFormula) :
    Provable (a ⇒ (b ⇒ LetterlessFormula.conj a b)) := by
  have h₁ : Provable (a ⇒ ((a ⇒ LetterlessFormula.neg b) ⇒ LetterlessFormula.neg b)) := by
    have hswap :
        Provable (((a ⇒ LetterlessFormula.neg b) ⇒ a ⇒ LetterlessFormula.neg b) ⇒
          (a ⇒ ((a ⇒ LetterlessFormula.neg b) ⇒ LetterlessFormula.neg b))) :=
      Provable.imp_swap (a ⇒ LetterlessFormula.neg b) a (LetterlessFormula.neg b)
    exact Provable.modusPonens hswap (Provable.imp_self (a ⇒ LetterlessFormula.neg b))
  have h₂ :
      Provable (a ⇒ (((a ⇒ LetterlessFormula.neg b) ⇒ (b ⇒ ⊥)) ⇒
        (b ⇒ ((a ⇒ LetterlessFormula.neg b) ⇒ ⊥)))) :=
    Provable.weaken (a := a)
      (Provable.imp_swap (a ⇒ LetterlessFormula.neg b) b ⊥)
  have h₃ :
      Provable (a ⇒ (b ⇒ ((a ⇒ LetterlessFormula.neg b) ⇒ ⊥))) :=
    Provable.imp_mp h₁ h₂
  simpa [LetterlessFormula.conj, LetterlessFormula.neg] using h₃

/--
Left distributivity of conjunction over the derived disjunction.
-/
theorem eqv_conj_disj_left (a b c : LetterlessFormula) :
    Provable.Eqv
      (LetterlessFormula.conj (LetterlessFormula.disj a b) c)
      (LetterlessFormula.disj (LetterlessFormula.conj a c) (LetterlessFormula.conj b c)) := by
  let d := LetterlessFormula.disj (LetterlessFormula.conj a c) (LetterlessFormula.conj b c)
  constructor
  · have hintroL : Provable (LetterlessFormula.conj a c ⇒ d) :=
      disj_intro_left (LetterlessFormula.conj a c) (LetterlessFormula.conj b c)
    have hintroR : Provable (LetterlessFormula.conj b c ⇒ d) :=
      disj_intro_right (LetterlessFormula.conj a c) (LetterlessFormula.conj b c)
    have hcurL : Provable (a ⇒ (c ⇒ LetterlessFormula.conj a c)) :=
      conj_intro_curried a c
    have hcurR : Provable (b ⇒ (c ⇒ LetterlessFormula.conj b c)) :=
      conj_intro_curried b c
    have hpostL : Provable ((c ⇒ LetterlessFormula.conj a c) ⇒ (c ⇒ d)) := by
      exact Provable.modusPonens
        (Provable.imp_compose c (LetterlessFormula.conj a c) d)
        hintroL
    have hpostR : Provable ((c ⇒ LetterlessFormula.conj b c) ⇒ (c ⇒ d)) := by
      exact Provable.modusPonens
        (Provable.imp_compose c (LetterlessFormula.conj b c) d)
        hintroR
    have hA : Provable (a ⇒ (c ⇒ d)) :=
      Provable.imp_mp hcurL (Provable.weaken (a := a) hpostL)
    have hB : Provable (b ⇒ (c ⇒ d)) :=
      Provable.imp_mp hcurR (Provable.weaken (a := b) hpostR)
    have hdisj : Provable (LetterlessFormula.disj a b ⇒ (c ⇒ d)) :=
      disj_elim hA hB
    have hleft :
        Provable (LetterlessFormula.conj (LetterlessFormula.disj a b) c ⇒
          LetterlessFormula.disj a b) :=
      conj_elim_left _ _
    have hright :
        Provable (LetterlessFormula.conj (LetterlessFormula.disj a b) c ⇒ c) :=
      conj_elim_right _ _
    have hstep :
        Provable (LetterlessFormula.conj (LetterlessFormula.disj a b) c ⇒ (c ⇒ d)) :=
      Provable.imp_trans hleft hdisj
    exact Provable.imp_mp hright hstep
  · have hLdisj :
        Provable (LetterlessFormula.conj a c ⇒ LetterlessFormula.disj a b) :=
      Provable.imp_trans (conj_elim_left _ _) (disj_intro_left a b)
    have hLc : Provable (LetterlessFormula.conj a c ⇒ c) :=
      conj_elim_right _ _
    have hRdisj :
        Provable (LetterlessFormula.conj b c ⇒ LetterlessFormula.disj a b) :=
      Provable.imp_trans (conj_elim_left _ _) (disj_intro_right a b)
    have hRc : Provable (LetterlessFormula.conj b c ⇒ c) :=
      conj_elim_right _ _
    have hL :
        Provable (LetterlessFormula.conj a c ⇒
          LetterlessFormula.conj (LetterlessFormula.disj a b) c) :=
      conj_intro _ _ _ hLdisj hLc
    have hR :
        Provable (LetterlessFormula.conj b c ⇒
          LetterlessFormula.conj (LetterlessFormula.disj a b) c) :=
      conj_intro _ _ _ hRdisj hRc
    exact disj_elim hL hR

/--
Conjunction of cofinite single-hole/finite-gap codes collapses to the cofinite
code for the union.
-/
theorem eqv_conj_cofiniteNormalForm_cons (n : Nat) (ns : List Nat) :
    Eqv (LetterlessFormula.conj
          (LetterlessFormula.cofiniteNormalForm [n])
          (LetterlessFormula.cofiniteNormalForm ns))
      (LetterlessFormula.cofiniteNormalForm (n :: ns)) := by
  have h₁ :
      Eqv (LetterlessFormula.conj
            (LetterlessFormula.cofiniteNormalForm [n])
            (LetterlessFormula.cofiniteNormalForm ns))
        (LetterlessFormula.conj
          (LetterlessFormula.neg (LetterlessFormula.pulseAt n))
          (LetterlessFormula.neg (LetterlessFormula.finiteNormalForm ns))) := by
    refine eqv_conj ?_ (eqv_refl _)
    simpa [LetterlessFormula.cofiniteNormalForm, LetterlessFormula.finiteNormalForm] using
      eqv_neg (eqv_disj_bottom (LetterlessFormula.pulseAt n))
  have h₂ :
      Eqv (LetterlessFormula.conj
            (LetterlessFormula.neg (LetterlessFormula.pulseAt n))
            (LetterlessFormula.neg (LetterlessFormula.finiteNormalForm ns)))
        (LetterlessFormula.neg
          (LetterlessFormula.disj (LetterlessFormula.pulseAt n)
            (LetterlessFormula.finiteNormalForm ns))) :=
    eqv_conj_neg_neg (LetterlessFormula.pulseAt n) (LetterlessFormula.finiteNormalForm ns)
  exact eqv_trans h₁ (by
    simpa [LetterlessFormula.cofiniteNormalForm, LetterlessFormula.finiteNormalForm])

/--
The adjacent clause is provably equivalent to the corresponding single-hole
cofinite normal form.
-/
theorem eqv_adjacentClause_singleHole (n : Nat) :
    Eqv (LetterlessFormula.adjacentClause n)
      (LetterlessFormula.cofiniteNormalForm [n]) := by
  simpa [LetterlessFormula.adjacentClause, iterClause,
    LetterlessFormula.cofiniteNormalForm, LetterlessFormula.finiteNormalForm,
    LetterlessFormula.disj, LetterlessFormula.neg, LetterlessFormula.pulseAt,
    LetterlessFormula.iterBoxBottom]
    using eqv_fourNeg (LetterlessFormula.adjacentClause n)

/--
Finite conjunctions of adjacent clauses are provably equivalent to the
corresponding conjunctions of single-hole cofinite normal forms.
-/
theorem eqv_adjacentClauseConjunction_holeConjunction (ns : List Nat) :
    Eqv (LetterlessFormula.adjacentClauseConjunction ns)
      (LetterlessFormula.holeConjunction ns) := by
  induction ns with
  | nil =>
      exact eqv_refl _
  | cons n ns ih =>
      simpa [LetterlessFormula.adjacentClauseConjunction, LetterlessFormula.holeConjunction]
        using eqv_conj (eqv_adjacentClause_singleHole n) ih

/--
Recursive adjacent spans are provably equivalent to the corresponding recursive
single-hole spans.
-/
theorem eqv_adjacentSpan_holeSpan (n k : Nat) :
    Eqv (LetterlessFormula.adjacentSpan n k) (LetterlessFormula.holeSpan n k) := by
  induction k generalizing n with
  | zero =>
      exact eqv_refl _
  | succ k ih =>
      simpa [LetterlessFormula.adjacentSpan, LetterlessFormula.holeSpan] using
        eqv_conj (eqv_adjacentClause_singleHole n) (ih (n + 1))

/--
Composition of implication clauses.
-/
theorem iterClause_compose (m p n : Nat) :
    Provable (iterClause p n ⇒ (iterClause m p ⇒ iterClause m n)) := by
  simpa [iterClause] using imp_compose (LetterlessFormula.iterBoxBottom m)
    (LetterlessFormula.iterBoxBottom p) (LetterlessFormula.iterBoxBottom n)

/--
A span of adjacent clauses yields the corresponding long clause.
-/
theorem adjacentSpan_implies_iterClause (n k : Nat) :
    Provable (LetterlessFormula.adjacentSpan n k ⇒ iterClause (n + k) n) := by
  induction k generalizing n with
  | zero =>
      have hclause : Provable (iterClause n n) :=
        provable_iterClause_of_le (Nat.le_refl n)
      simpa [LetterlessFormula.adjacentSpan] using weaken (a := LetterlessFormula.top) hclause
  | succ k ih =>
      have hleft :
          Provable (LetterlessFormula.adjacentSpan n (k + 1) ⇒ LetterlessFormula.adjacentClause n) :=
        by
          simpa [LetterlessFormula.adjacentSpan] using
            conj_elim_left (LetterlessFormula.adjacentClause n)
              (LetterlessFormula.adjacentSpan (n + 1) k)
      have hright :
          Provable (LetterlessFormula.adjacentSpan n (k + 1) ⇒
            iterClause (n + 1 + k) (n + 1)) := by
        have hproj :
            Provable (LetterlessFormula.adjacentSpan n (k + 1) ⇒
              LetterlessFormula.adjacentSpan (n + 1) k) := by
          simpa [LetterlessFormula.adjacentSpan] using
            conj_elim_right (LetterlessFormula.adjacentClause n)
              (LetterlessFormula.adjacentSpan (n + 1) k)
        exact imp_trans hproj (ih (n + 1))
      have hstep :
          Provable (LetterlessFormula.adjacentSpan n (k + 1) ⇒
            (LetterlessFormula.adjacentClause n ⇒
              (iterClause (n + 1 + k) (n + 1) ⇒ iterClause (n + 1 + k) n))) := by
        exact weaken (a := LetterlessFormula.adjacentSpan n (k + 1))
          (iterClause_compose (n + 1 + k) (n + 1) n)
      have hstep' :
          Provable (LetterlessFormula.adjacentSpan n (k + 1) ⇒
            (iterClause (n + 1 + k) (n + 1) ⇒ iterClause (n + 1 + k) n)) :=
        imp_mp hleft hstep
      have htail :
          Provable (LetterlessFormula.adjacentSpan n (k + 1) ⇒
            iterClause (n + 1 + k) n) :=
        imp_mp hright hstep'
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/--
The corresponding recursive single-hole span also yields the long clause.
-/
theorem holeSpan_implies_iterClause (n k : Nat) :
    Provable (LetterlessFormula.holeSpan n k ⇒ iterClause (n + k) n) := by
  have h₁ : Provable (LetterlessFormula.holeSpan n k ⇒ LetterlessFormula.adjacentSpan n k) :=
    (eqv_adjacentSpan_holeSpan n k).2
  exact imp_trans h₁ (adjacentSpan_implies_iterClause n k)

/--
A long clause implies its first adjacent clause.
-/
theorem iterClause_implies_adjacentClause (n k : Nat) :
    Provable (iterClause (n + (k + 1)) n ⇒ LetterlessFormula.adjacentClause n) := by
  have hmono :
      Provable (LetterlessFormula.iterBoxBottom (n + 1) ⇒
        LetterlessFormula.iterBoxBottom (n + (k + 1))) := by
    have hle : n + 1 ≤ n + (k + 1) := by
      simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      provable_iterBoxBottom_monotone (n := n + 1) (m := n + (k + 1))
        hle
  simpa [LetterlessFormula.adjacentClause, iterClause, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    imp_postcompose (a := LetterlessFormula.iterBoxBottom (n + 1))
      (b := LetterlessFormula.iterBoxBottom (n + (k + 1)))
      (c := LetterlessFormula.iterBoxBottom n) hmono

/--
A long clause implies its tail clause.
-/
theorem iterClause_implies_tailClause (n k : Nat) :
    Provable (iterClause (n + (k + 1)) n ⇒ iterClause (n + (k + 1)) (n + 1)) := by
  have hstep : Provable (LetterlessFormula.iterBoxBottom n ⇒ LetterlessFormula.iterBoxBottom (n + 1)) := by
    simpa using provable_iterBoxBottom_step n
  simpa [iterClause] using
    Provable.modusPonens
      (imp_compose (LetterlessFormula.iterBoxBottom (n + (k + 1)))
        (LetterlessFormula.iterBoxBottom n)
        (LetterlessFormula.iterBoxBottom (n + 1)))
      hstep

/--
The long clause yields its corresponding recursive single-hole span.
-/
theorem iterClause_implies_holeSpan (n k : Nat) :
    Provable (iterClause (n + k) n ⇒ LetterlessFormula.holeSpan n k) := by
  induction k generalizing n with
  | zero =>
      exact weaken (a := iterClause n n) provable_top
  | succ k ih =>
      have hhead :
          Provable (iterClause (n + (k + 1)) n ⇒ LetterlessFormula.cofiniteNormalForm [n]) := by
        exact imp_trans (iterClause_implies_adjacentClause n k) (eqv_adjacentClause_singleHole n).1
      have htail :
          Provable (iterClause (n + (k + 1)) n ⇒ LetterlessFormula.holeSpan (n + 1) k) := by
        exact imp_trans (iterClause_implies_tailClause n k)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (ih (n + 1)))
      simpa [LetterlessFormula.holeSpan] using
        conj_intro (iterClause (n + (k + 1)) n)
          (LetterlessFormula.cofiniteNormalForm [n])
          (LetterlessFormula.holeSpan (n + 1) k)
          hhead htail

/--
A long clause is provably equivalent to its recursive single-hole span.
-/
theorem eqv_iterClause_holeSpan (n k : Nat) :
    Eqv (iterClause (n + k) n) (LetterlessFormula.holeSpan n k) :=
  ⟨iterClause_implies_holeSpan n k, holeSpan_implies_iterClause n k⟩

/--
General clause equivalence to recursive single-hole span form.
-/
theorem eqv_iterClause_holeSpan_general {m n : Nat} (h : n ≤ m) :
    Eqv (iterClause m n) (LetterlessFormula.holeSpan n (m - n)) := by
  simpa [Nat.add_sub_of_le h] using eqv_iterClause_holeSpan n (m - n)

/--
Recursive single-hole spans are provably equivalent to the explicit cofinite
normal forms on the corresponding intervals.
-/
theorem eqv_holeSpan_cofiniteRange (n k : Nat) :
    Eqv (LetterlessFormula.holeSpan n k)
      (LetterlessFormula.cofiniteNormalForm (List.range' n k)) := by
  induction k generalizing n with
  | zero =>
      exact eqv_refl _
  | succ k ih =>
      have h₁ :
          Eqv (LetterlessFormula.holeSpan n (k + 1))
            (LetterlessFormula.conj
              (LetterlessFormula.cofiniteNormalForm [n])
              (LetterlessFormula.cofiniteNormalForm (List.range' (n + 1) k))) := by
        simpa [LetterlessFormula.holeSpan] using eqv_conj (eqv_refl _) (ih (n + 1))
      have h₂ :
          Eqv (LetterlessFormula.conj
                (LetterlessFormula.cofiniteNormalForm [n])
                (LetterlessFormula.cofiniteNormalForm (List.range' (n + 1) k)))
              (LetterlessFormula.cofiniteNormalForm (n :: List.range' (n + 1) k)) :=
        eqv_conj_cofiniteNormalForm_cons n (List.range' (n + 1) k)
      have h₃ :
          Eqv (LetterlessFormula.cofiniteNormalForm (n :: List.range' (n + 1) k))
              (LetterlessFormula.cofiniteNormalForm (List.range' n (k + 1))) := by
        simpa [List.range'_succ] using eqv_refl
          (LetterlessFormula.cofiniteNormalForm (n :: List.range' (n + 1) k))
      exact eqv_trans (eqv_trans h₁ h₂) h₃

end Provable

/--
Boolos-style normal forms, phrased directly in bitstream language: a finite set
of true times, or the complement of a finite set of false times.
-/
inductive NormalForm where
  | finite : List Nat → NormalForm
  | cofinite : List Nat → NormalForm

namespace NormalForm

def toFormula : NormalForm → LetterlessFormula
  | finite ns => LetterlessFormula.finiteNormalForm ns
  | cofinite ns => LetterlessFormula.cofiniteNormalForm ns

theorem eval_toFormula : ∀ nf : NormalForm,
    LetterlessFormula.eval nf.toFormula =
      match nf with
      | finite ns => fun t => decide (t ∈ ns)
      | cofinite ns => fun t => decide (t ∉ ns)
  | finite ns => LetterlessFormula.eval_finiteNormalForm ns
  | cofinite ns => LetterlessFormula.eval_cofiniteNormalForm ns

def supportBefore (N : Nat) (s : Bitstream) : List Nat :=
  (List.range N).filter fun t => s t = true

def holesBefore (N : Nat) (s : Bitstream) : List Nat :=
  (List.range N).filter fun t => s t = false

theorem mem_supportBefore_iff (N : Nat) (s : Bitstream) (t : Nat) :
    t ∈ supportBefore N s ↔ t < N ∧ s t = true := by
  simp [supportBefore]

theorem mem_holesBefore_iff (N : Nat) (s : Bitstream) (t : Nat) :
    t ∈ holesBefore N s ↔ t < N ∧ s t = false := by
  simp [holesBefore]

def ofEventuallyConstantData (N : Nat) (s : Bitstream) (b : Bit) : NormalForm :=
  if b then cofinite (holesBefore N s) else finite (supportBefore N s)

theorem eval_ofEventuallyConstantData
    (N : Nat) (s : Bitstream) (b : Bit)
    (hstab : ∀ t, N ≤ t → s t = b) :
    LetterlessFormula.eval (ofEventuallyConstantData N s b).toFormula = s := by
  funext t
  by_cases hb : b
  · simp [ofEventuallyConstantData, hb, eval_toFormula]
    by_cases ht : t < N
    · cases hs : s t with
      | false =>
          have hmem : t ∈ holesBefore N s :=
            (mem_holesBefore_iff N s t).2 ⟨ht, hs⟩
          simp [hmem]
      | true =>
          have hnot : t ∉ holesBefore N s := by
            intro hmem
            have : s t = false := (mem_holesBefore_iff N s t).mp hmem |>.2
            simp [hs] at this
          simp [hnot]
    · have hge : N ≤ t := Nat.le_of_not_gt ht
      have hs : s t = true := by simpa [hb] using hstab t hge
      have hnot : t ∉ holesBefore N s := by
        intro hmem
        exact Nat.not_lt_of_ge hge ((mem_holesBefore_iff N s t).mp hmem).1
      simp [hs, hnot]
  · simp [ofEventuallyConstantData, hb, eval_toFormula]
    by_cases ht : t < N
    · have hmem : t ∈ supportBefore N s ↔ s t = true := by
        constructor
        · intro hmem'
          exact (mem_supportBefore_iff N s t).mp hmem' |>.2
        · intro htrue
          exact (mem_supportBefore_iff N s t).2 ⟨ht, htrue⟩
      cases hs : s t <;> simp [hs, hmem]
    · have hge : N ≤ t := Nat.le_of_not_gt ht
      have hs : s t = false := by simpa [hb] using hstab t hge
      have hnot : t ∉ supportBefore N s := by
        intro hmem
        exact Nat.not_lt_of_ge hge ((mem_supportBefore_iff N s t).mp hmem).1
      simp [hs, hnot]

theorem exists_of_eventuallyConstant (s : Bitstream) (hs : EventuallyConstant s) :
    ∃ nf : NormalForm, LetterlessFormula.eval nf.toFormula = s := by
  rcases hs with ⟨N, b, hstab⟩
  exact ⟨ofEventuallyConstantData N s b, eval_ofEventuallyConstantData N s b hstab⟩

theorem eventuallyConstant_toFormula (nf : NormalForm) :
    EventuallyConstant (LetterlessFormula.eval nf.toFormula) := by
  have hguard : OneLetterFormula.guarded (OneLetterFormula.ofLetterless nf.toFormula) :=
    OneLetterFormula.guarded_ofLetterless nf.toFormula
  have hstable :
      EventuallyConstant
        (OneLetterFormula.eval const0 (OneLetterFormula.ofLetterless nf.toFormula)) :=
    OneLetterFormula.eval_eventuallyConstant
      (OneLetterFormula.ofLetterless nf.toFormula) hguard const0
  have heq :
      OneLetterFormula.eval const0 (OneLetterFormula.ofLetterless nf.toFormula) =
        LetterlessFormula.eval nf.toFormula :=
    OneLetterFormula.eval_ofLetterless nf.toFormula const0
  simpa [heq] using hstable

/--
Finite-list difference, used in explicit normal-form implication.
-/
def diff (xs ys : List Nat) : List Nat :=
  xs.filter fun x => decide (x ∉ ys)

theorem mem_diff_iff (xs ys : List Nat) (t : Nat) :
    t ∈ diff xs ys ↔ t ∈ xs ∧ t ∉ ys := by
  simp [diff]

/--
Finite-list intersection, used in explicit normal-form implication.
-/
def inter (xs ys : List Nat) : List Nat :=
  xs.filter fun x => decide (x ∈ ys)

theorem mem_inter_iff (xs ys : List Nat) (t : Nat) :
    t ∈ inter xs ys ↔ t ∈ xs ∧ t ∈ ys := by
  simp [inter]

/--
Explicit implication on normal forms.
-/
def imp : NormalForm → NormalForm → NormalForm
  | finite xs, finite ys => cofinite (diff xs ys)
  | finite xs, cofinite ys => cofinite (inter xs ys)
  | cofinite xs, finite ys => finite (xs ++ ys)
  | cofinite xs, cofinite ys => cofinite (diff ys xs)

theorem eval_imp (p q : NormalForm) :
    LetterlessFormula.eval (imp p q).toFormula =
      (LetterlessFormula.eval p.toFormula =⇒ LetterlessFormula.eval q.toFormula) := by
  cases p <;> cases q <;> funext t <;>
    simp [imp, eval_toFormula, bimplies, mem_diff_iff, mem_inter_iff,
      List.mem_append, Bool.or_comm]

/--
Explicit normal form attached to a Boolos-style implication clause.
-/
def ofIterClause (m n : Nat) : NormalForm :=
  if m ≤ n then cofinite [] else cofinite (LetterlessFormula.clauseGap m n)

theorem eval_ofIterClause (m n : Nat) :
    LetterlessFormula.eval (ofIterClause m n).toFormula =
      LetterlessFormula.eval (iterClause m n) := by
  by_cases h : m ≤ n
  · have heqTop :
        LetterlessFormula.eval (iterClause m n) = const1 := by
      funext t
      rw [eval_iterClause]
      have htrue : m ≤ t ∨ t < n := by
        by_cases htn : t < n
        · exact Or.inr htn
        · exact Or.inl (Nat.le_trans h (Nat.le_of_not_gt htn))
      simp [htrue, const1, const]
    rw [ofIterClause, if_pos h]
    calc
      LetterlessFormula.eval (toFormula (cofinite [])) = const1 := by
        funext t
        rfl
      _ = LetterlessFormula.eval (iterClause m n) := heqTop.symm
  · rw [ofIterClause, if_neg h]
    simpa [toFormula] using (LetterlessFormula.eval_iterClause_as_cofiniteNormalForm m n).symm

/--
Conjunction of a finite list of Boolos-style clauses.
-/
def clauseConjunction : List (Nat × Nat) → LetterlessFormula
  | [] => LetterlessFormula.top
  | (m, n) :: cs => LetterlessFormula.conj (iterClause m n) (clauseConjunction cs)

/--
The clause conjunction obtained by replacing each clause with its explicit
normal-form representative.
-/
def normalizedClauseConjunction : List (Nat × Nat) → LetterlessFormula
  | [] => LetterlessFormula.top
  | (m, n) :: cs => LetterlessFormula.conj (ofIterClause m n).toFormula
      (normalizedClauseConjunction cs)

/--
Proof-theoretic clause normal form using recursive single-hole spans.
-/
def spanOfIterClause (m n : Nat) : LetterlessFormula :=
  if m ≤ n then LetterlessFormula.top else LetterlessFormula.holeSpan n (m - n)

/--
Conjunction of clauses normalized into recursive single-hole span form.
-/
def spanClauseConjunction : List (Nat × Nat) → LetterlessFormula
  | [] => LetterlessFormula.top
  | (m, n) :: cs => LetterlessFormula.conj (spanOfIterClause m n)
      (spanClauseConjunction cs)

theorem eval_spanOfIterClause (m n : Nat) :
    LetterlessFormula.eval (spanOfIterClause m n) =
      LetterlessFormula.eval (iterClause m n) := by
  by_cases h : m ≤ n
  · rw [spanOfIterClause, if_pos h]
    funext t
    have htrue : m ≤ t ∨ t < n := by
      by_cases htn : t < n
      · exact Or.inr htn
      · exact Or.inl (Nat.le_trans h (Nat.le_of_not_gt htn))
    simp [LetterlessFormula.eval_top, eval_iterClause, htrue, const1, const]
  · rw [spanOfIterClause, if_neg h]
    simpa using (LetterlessFormula.eval_iterClause_as_holeSpan n (m - n)).symm.trans
      (by
        have hle : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge h)
        simp [Nat.add_sub_of_le hle])

/--
The corresponding normal form obtained by unioning the finite gaps.
-/
def normalFormOfClauseConjunction : List (Nat × Nat) → NormalForm
  | [] => cofinite []
  | (m, n) :: cs =>
      match ofIterClause m n, normalFormOfClauseConjunction cs with
      | cofinite ns, cofinite ms => cofinite (ns ++ ms)
      | _, _ => cofinite []

theorem ofIterClause_is_cofinite (m n : Nat) :
    ∃ ns, ofIterClause m n = cofinite ns := by
  by_cases h : m ≤ n
  · exact ⟨[], by simp [ofIterClause, h]⟩
  · exact ⟨LetterlessFormula.clauseGap m n, by simp [ofIterClause, h]⟩

theorem normalFormOfClauseConjunction_is_cofinite (cs : List (Nat × Nat)) :
    ∃ ns, normalFormOfClauseConjunction cs = cofinite ns := by
  induction cs with
  | nil =>
      exact ⟨[], rfl⟩
  | cons c cs ih =>
      rcases c with ⟨m, n⟩
      rcases ofIterClause_is_cofinite m n with ⟨ns, hns⟩
      rcases ih with ⟨ms, hms⟩
      refine ⟨ns ++ ms, ?_⟩
      simp [normalFormOfClauseConjunction, hns, hms]

theorem eval_clauseConjunction (cs : List (Nat × Nat)) :
    LetterlessFormula.eval (clauseConjunction cs) =
      LetterlessFormula.eval (normalFormOfClauseConjunction cs).toFormula := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      rcases c with ⟨m, n⟩
      rcases normalFormOfClauseConjunction_is_cofinite cs with ⟨ms, hms⟩
      rw [clauseConjunction, LetterlessFormula.eval_conj, ih, hms]
      rw [show LetterlessFormula.eval (iterClause m n) =
          LetterlessFormula.eval (ofIterClause m n).toFormula by
            exact (eval_ofIterClause m n).symm]
      rcases ofIterClause_is_cofinite m n with ⟨ns, hns⟩
      rw [hns]
      calc
        LetterlessFormula.eval (toFormula (cofinite ns)) &&&
            LetterlessFormula.eval (toFormula (cofinite ms))
            =
            LetterlessFormula.eval
              (LetterlessFormula.cofiniteNormalForm ns &&&
                LetterlessFormula.cofiniteNormalForm ms) := by
              symm
              exact LetterlessFormula.eval_conj
                (LetterlessFormula.cofiniteNormalForm ns)
                (LetterlessFormula.cofiniteNormalForm ms)
        _ = LetterlessFormula.eval
              (LetterlessFormula.cofiniteNormalForm (ns ++ ms)) :=
              LetterlessFormula.eval_conj_cofiniteNormalForm ns ms
        _ = LetterlessFormula.eval (toFormula (cofinite (ns ++ ms))) := by
              rfl
        _ = LetterlessFormula.eval (normalFormOfClauseConjunction ((m, n) :: cs)).toFormula := by
              simp [normalFormOfClauseConjunction, hns, hms]

/--
Semantically, replacing each clause by its explicit normal-form representative
does not change the denotation of the whole conjunction.
-/
theorem eval_normalizedClauseConjunction (cs : List (Nat × Nat)) :
    LetterlessFormula.eval (normalizedClauseConjunction cs) =
      LetterlessFormula.eval (clauseConjunction cs) := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      rcases c with ⟨m, n⟩
      rw [normalizedClauseConjunction, clauseConjunction, LetterlessFormula.eval_conj,
        LetterlessFormula.eval_conj, ih, eval_ofIterClause]

/--
Semantically, the span-normalized clause conjunction has the same denotation as
the original clause conjunction.
-/
theorem eval_spanClauseConjunction (cs : List (Nat × Nat)) :
    LetterlessFormula.eval (spanClauseConjunction cs) =
      LetterlessFormula.eval (clauseConjunction cs) := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      rcases c with ⟨m, n⟩
      rw [spanClauseConjunction, clauseConjunction, LetterlessFormula.eval_conj,
        LetterlessFormula.eval_conj, ih, eval_spanOfIterClause]

/--
In the monotone case `m ≤ n`, a clause is provably equivalent to its explicit
normal-form representative.
-/
theorem eqv_iterClause_ofIterClause_of_le {m n : Nat} (h : m ≤ n) :
    Provable.Eqv (iterClause m n) (ofIterClause m n).toFormula := by
  rw [ofIterClause, if_pos h]
  simpa [NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm,
    LetterlessFormula.finiteNormalForm, LetterlessFormula.neg, LetterlessFormula.top] using
    eqv_iterClause_top_of_le h

/--
Every clause is provably equivalent to its explicit finite/cofinite normal-form
representative.
-/
theorem eqv_iterClause_ofIterClause (m n : Nat) :
    Provable.Eqv (iterClause m n) (ofIterClause m n).toFormula := by
  by_cases h : m ≤ n
  · exact eqv_iterClause_ofIterClause_of_le h
  · rw [ofIterClause, if_neg h]
    have hle : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge h)
    have h₁ : Provable.Eqv (iterClause m n) (LetterlessFormula.holeSpan n (m - n)) :=
      Provable.eqv_iterClause_holeSpan_general hle
    have h₂ :
        Provable.Eqv (LetterlessFormula.holeSpan n (m - n))
          (LetterlessFormula.cofiniteNormalForm (List.range' n (m - n))) :=
      Provable.eqv_holeSpan_cofiniteRange n (m - n)
    simpa [NormalForm.toFormula, LetterlessFormula.clauseGap_eq_range' hle] using
      (Provable.eqv_trans h₁ h₂)

/--
Every clause is provably equivalent to its recursive span normal form.
-/
theorem eqv_iterClause_spanOfIterClause (m n : Nat) :
    Provable.Eqv (iterClause m n) (spanOfIterClause m n) := by
  by_cases h : m ≤ n
  · rw [spanOfIterClause, if_pos h]
    exact eqv_iterClause_top_of_le h
  · rw [spanOfIterClause, if_neg h]
    exact Provable.eqv_iterClause_holeSpan_general (Nat.le_of_lt (Nat.lt_of_not_ge h))

/--
If each clause is provably equivalent to its explicit normal-form
representative, then so is the whole finite conjunction.
-/
theorem eqv_clauseConjunction_normalized
    (cs : List (Nat × Nat))
    (hcs : ∀ c ∈ cs,
      Provable.Eqv (iterClause c.1 c.2) (ofIterClause c.1 c.2).toFormula) :
    Provable.Eqv (clauseConjunction cs) (normalizedClauseConjunction cs) := by
  induction cs with
  | nil =>
      exact Provable.eqv_refl _
  | cons c cs ih =>
      rcases c with ⟨m, n⟩
      have hhead : Provable.Eqv (iterClause m n) (ofIterClause m n).toFormula :=
        hcs (m, n) (by simp)
      have htail :
          Provable.Eqv (clauseConjunction cs) (normalizedClauseConjunction cs) := by
        apply ih
        intro c' hc'
        exact hcs c' (List.mem_cons_of_mem _ hc')
      simpa [clauseConjunction, normalizedClauseConjunction] using
        Provable.eqv_conj hhead htail

/--
As a first fully proof-theoretic normalization result, if every clause is one
of the trivial monotone cases `m ≤ n`, then the whole conjunction is provably
equivalent to the conjunction of its explicit normal-form representatives.
-/
theorem eqv_clauseConjunction_normalized_of_all_le
    (cs : List (Nat × Nat))
    (hcs : ∀ c ∈ cs, c.1 ≤ c.2) :
    Provable.Eqv (clauseConjunction cs) (normalizedClauseConjunction cs) := by
  apply eqv_clauseConjunction_normalized
  intro c hc
  exact eqv_iterClause_ofIterClause_of_le (hcs c hc)

/--
Every finite conjunction of clauses is provably equivalent to the conjunction
of their explicit finite/cofinite normal-form representatives.
-/
theorem eqv_clauseConjunction_normalized_all
    (cs : List (Nat × Nat)) :
    Provable.Eqv (clauseConjunction cs) (normalizedClauseConjunction cs) := by
  apply eqv_clauseConjunction_normalized
  intro c hc
  exact eqv_iterClause_ofIterClause c.1 c.2

/--
Every finite conjunction of clauses is provably equivalent to its recursive
span-normalized form.
-/
theorem eqv_clauseConjunction_spanNormalized
    (cs : List (Nat × Nat)) :
    Provable.Eqv (clauseConjunction cs) (spanClauseConjunction cs) := by
  induction cs with
  | nil =>
      exact Provable.eqv_refl _
  | cons c cs ih =>
      rcases c with ⟨m, n⟩
      simpa [clauseConjunction, spanClauseConjunction] using
        Provable.eqv_conj (eqv_iterClause_spanOfIterClause m n) ih

end NormalForm

/--
Every letterless formula has a Boolos-style finite/cofinite normal form with
the same bitstream denotation.
-/
theorem exists_normalForm (a : LetterlessFormula) :
    ∃ nf : NormalForm, LetterlessFormula.eval nf.toFormula = LetterlessFormula.eval a := by
  have hguard : OneLetterFormula.guarded (OneLetterFormula.ofLetterless a) :=
    OneLetterFormula.guarded_ofLetterless a
  have hstable :
      EventuallyConstant
        (OneLetterFormula.eval const0 (OneLetterFormula.ofLetterless a)) :=
    OneLetterFormula.eval_eventuallyConstant
      (OneLetterFormula.ofLetterless a) hguard const0
  have heq :
      OneLetterFormula.eval const0 (OneLetterFormula.ofLetterless a) =
        LetterlessFormula.eval a :=
    OneLetterFormula.eval_ofLetterless a const0
  exact NormalForm.exists_of_eventuallyConstant _ (by simpa [heq] using hstable)

/--
A chosen normal form for a letterless formula.
-/
noncomputable def normalFormOf (a : LetterlessFormula) : NormalForm :=
  Classical.choose (exists_normalForm a)

/--
The chosen normal form has the same denotation as the original formula.
-/
theorem eval_normalFormOf (a : LetterlessFormula) :
    LetterlessFormula.eval (normalFormOf a).toFormula = LetterlessFormula.eval a :=
  Classical.choose_spec (exists_normalForm a)

/--
A `FirstFalse s` witness records the least index where a bitstream `s` is false.
-/
structure FirstFalse (s : Bitstream) where
  idx : Nat
  false_at : s idx = false
  before_true : ∀ k, k < idx → s k = true

/--
Every `box` stream is either constantly true or has a first false time.
-/
theorem box_all_true_or_exists_first_false (s : Bitstream) :
    (Bitstream.box s = const1) ∨
      ∃ _ : FirstFalse (Bitstream.box s), True := by
  by_cases hall : ∀ t, Bitstream.box s t = true
  · left
    funext t
    simp [const1, const, hall t]
  · right
    have hex : ∃ t, Bitstream.box s t = false := by
      by_cases h : ∃ t, Bitstream.box s t = false
      · exact h
      · exfalso
        apply hall
        intro t
        cases hbt : Bitstream.box s t with
        | false =>
            exact False.elim (h ⟨t, hbt⟩)
        | true =>
            simp
    rcases hex with ⟨t, ht⟩
    clear hall
    induction t with
    | zero =>
        exact ⟨⟨0, ht, by intro k hk; exact False.elim (Nat.not_lt_zero _ hk)⟩, trivial⟩
    | succ t ih =>
        by_cases hprev : Bitstream.box s t = false
        · rcases ih hprev with ⟨ff, -⟩
          exact ⟨ff, trivial⟩
        · refine ⟨⟨t + 1, ht, ?_⟩, trivial⟩
          intro k hk
          have hk' : k ≤ t := Nat.le_of_lt_succ hk
          by_cases hkt : k = t
          · simpa [hkt] using hprev
          · exact by
              have hklt : k < t := Nat.lt_of_le_of_ne hk' hkt
              have htrue : Bitstream.box s k ≠ false := by
                intro hkfalse
                have hstay := Bitstream.box_stays_false hkfalse (t - k)
                have hEq : k + (t - k) = t := Nat.add_sub_of_le hk'
                exact hprev (by simpa [hEq] using hstay)
              cases hbk : Bitstream.box s k with
              | false => exact False.elim (htrue hbk)
              | true => simp

/--
Package the previous theorem using the explicit `FirstFalse` witness.
-/
theorem box_all_true_or_exists_firstFalse (s : Bitstream) :
    (Bitstream.box s = const1) ∨ ∃ _ : FirstFalse (Bitstream.box s), True := by
  rcases box_all_true_or_exists_first_false s with hall | ⟨ff, -⟩
  · exact Or.inl hall
  · exact Or.inr ⟨ff, trivial⟩

/--
The finite normal form on `List.range n` denotes the initial segment `t < n`.
-/
theorem eval_finite_range (n : Nat) :
    LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula =
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
  funext t
  simp [NormalForm.toFormula, LetterlessFormula.eval_finiteNormalForm,
    LetterlessFormula.eval_iterBoxBottom]

/--
Every `box` stream is denoted by a canonical initial-segment/cofinite-empty
normal form.
-/
theorem box_has_initialSegment_normalForm (s : Bitstream) :
    ∃ nf : NormalForm, LetterlessFormula.eval nf.toFormula = Bitstream.box s := by
  rcases box_all_true_or_exists_firstFalse s with hall | ⟨ff, -⟩
  · exact ⟨NormalForm.cofinite [], by simpa [NormalForm.toFormula] using hall.symm⟩
  · refine ⟨NormalForm.finite (List.range ff.idx), ?_⟩
    funext t
    by_cases ht : t < ff.idx
    · have htrue : Bitstream.box s t = true := ff.before_true t ht
      simp [eval_finite_range, LetterlessFormula.eval_iterBoxBottom, ht, htrue]
    · have hge : ff.idx ≤ t := Nat.le_of_not_gt ht
      have hfalse : Bitstream.box s t = false := by
        have hstay := Bitstream.box_stays_false ff.false_at (t - ff.idx)
        simpa [Nat.add_sub_of_le hge] using hstay
      simp [eval_finite_range, LetterlessFormula.eval_iterBoxBottom, ht, hfalse]

/--
If a `box` stream is not constantly true, it has a first false time.
-/
theorem exists_first_false_of_not_all_true (s : Bitstream)
    (hall : ¬ ∀ t, Bitstream.box s t = true) :
    ∃ _ : FirstFalse (Bitstream.box s), True := by
  rcases box_all_true_or_exists_firstFalse s with hconst | hfirst
  · apply False.elim
    apply hall
    intro t
    simpa [const1, const] using congrArg (fun f => f t) hconst
  · exact hfirst

/--
Choose the first false time of `box s` once we know `box s` is not constantly
true.
-/
noncomputable def firstFalseOfNotAllTrue (s : Bitstream)
    (hall : ¬ ∀ t, Bitstream.box s t = true) : FirstFalse (Bitstream.box s) :=
  Classical.choose (exists_first_false_of_not_all_true s hall)

/--
The first false time of a boxed stream is unique.
-/
theorem first_false_unique {s : Bitstream} {m n : Nat}
    (hmfalse : Bitstream.box s m = false)
    (hmbefore : ∀ k, k < m → Bitstream.box s k = true)
    (hnfalse : Bitstream.box s n = false)
    (hnbefore : ∀ k, k < n → Bitstream.box s k = true) :
    m = n := by
  by_cases hmn : m = n
  · exact hmn
  · rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
    · have hmtrue : Bitstream.box s m = true := hnbefore m hlt
      simp [hmfalse] at hmtrue
    · have hntrue : Bitstream.box s n = true := hmbefore n hgt
      simp [hnfalse] at hntrue

/--
Any two first-false witnesses for the same boxed stream have the same index.
-/
theorem FirstFalse.unique_box {s : Bitstream}
    (ff₁ ff₂ : FirstFalse (Bitstream.box s)) :
    ff₁.idx = ff₂.idx :=
  first_false_unique ff₁.false_at ff₁.before_true ff₂.false_at ff₂.before_true

/--
If a bitstream is false somewhere, it has a first false time.
-/
theorem exists_first_false_of_exists_false (s : Bitstream)
    (hex : ∃ t, s t = false) :
    ∃ _ : FirstFalse s, True := by
  rcases hex with ⟨t, ht⟩
  have hmain : ∀ t : Nat, s t = false →
      ∃ _ : FirstFalse s, True := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
        intro ht
        by_cases hexprev : ∃ k, k < t ∧ s k = false
        · rcases hexprev with ⟨k, hklt, hkfalse⟩
          exact ih k hklt hkfalse
        · refine ⟨⟨t, ht, ?_⟩, trivial⟩
          intro k hk
          have hnotfalse : s k ≠ false := by
            intro hkfalse
            exact hexprev ⟨k, hk, hkfalse⟩
          cases hs : s k with
          | false => exact False.elim (hnotfalse hs)
          | true => simp
  exact hmain t ht

/--
Choose the least false index of a stream once some false index exists.
-/
noncomputable def firstFalseOfExistsFalse (s : Bitstream)
    (hex : ∃ t, s t = false) : FirstFalse s :=
  Classical.choose (exists_first_false_of_exists_false s hex)

/--
If `box s` has first false time `n`, then it denotes the initial segment
`□^n ⊥`.
-/
theorem eval_box_eq_iterBoxBottom_of_box_first_false
    (s : Bitstream) (n : Nat)
    (hnfalse : Bitstream.box s n = false)
    (hbefore : ∀ k, k < n → Bitstream.box s k = true) :
    Bitstream.box s = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
  funext t
  by_cases ht : t < n
  · have htrue : Bitstream.box s t = true := hbefore t ht
    have hiterTrue :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) t = true :=
      (LetterlessFormula.eval_iterBoxBottom_true_iff n t).2 ht
    simp [htrue, hiterTrue]
  · have hge : n ≤ t := Nat.le_of_not_gt ht
    have hfalse : Bitstream.box s t = false := by
      have hstay := Bitstream.box_stays_false hnfalse (t - n)
      simpa [Nat.add_sub_of_le hge] using hstay
    have hiterFalse :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) t = false := by
      cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) t with
      | false => exact rfl
      | true =>
          exact False.elim
            (Nat.not_lt_of_ge hge
              ((LetterlessFormula.eval_iterBoxBottom_true_iff n t).1 hval))
    simp [hfalse, hiterFalse]

/--
The previous theorem packaged with an explicit `FirstFalse` witness.
-/
theorem eval_box_eq_iterBoxBottom_of_box_firstFalse
    (s : Bitstream) (ff : FirstFalse (Bitstream.box s)) :
    Bitstream.box s = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom ff.idx) :=
  eval_box_eq_iterBoxBottom_of_box_first_false s ff.idx ff.false_at ff.before_true

/--
Canonical `□` on normal forms, using the initial-segment characterization of
`box`.
-/
noncomputable def NormalForm.box (p : NormalForm) : NormalForm := by
  classical
  exact
    if hall : ∀ t, Bitstream.box (LetterlessFormula.eval p.toFormula) t = true then
      NormalForm.cofinite []
    else
      let ff := firstFalseOfNotAllTrue (LetterlessFormula.eval p.toFormula) hall
      NormalForm.finite (List.range ff.idx)

theorem NormalForm.eval_box (p : NormalForm) :
    LetterlessFormula.eval (p.box).toFormula =
      Bitstream.box (LetterlessFormula.eval p.toFormula) := by
  classical
  by_cases hall : ∀ t, Bitstream.box (LetterlessFormula.eval p.toFormula) t = true
  · simp [NormalForm.box, hall]
    funext t
    have htrue : Bitstream.box (LetterlessFormula.eval p.toFormula) t = true := hall t
    simpa [NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm,
      LetterlessFormula.eval_neg, LetterlessFormula.eval_finiteNormalForm, const1, const, bnot]
      using htrue
  · let ff : FirstFalse (Bitstream.box (LetterlessFormula.eval p.toFormula)) :=
      firstFalseOfNotAllTrue (LetterlessFormula.eval p.toFormula) hall
    let n : Nat := ff.idx
    have hn : n = ff.idx := rfl
    simp [NormalForm.box, hall]
    have hnfalse :
        Bitstream.box (LetterlessFormula.eval p.toFormula) n = false :=
      ff.false_at
    have hbefore :
        ∀ k, k < n → Bitstream.box (LetterlessFormula.eval p.toFormula) k = true :=
      ff.before_true
    funext t
    by_cases ht : t < n
    · have htrue : Bitstream.box (LetterlessFormula.eval p.toFormula) t = true := hbefore t ht
      have ht' :
          t < (firstFalseOfNotAllTrue (LetterlessFormula.eval p.toFormula) hall).idx := by
        simpa [ff, n] using ht
      rw [NormalForm.toFormula, LetterlessFormula.eval_finiteNormalForm]
      simp [List.mem_range, ht', htrue]
    · have hge : n ≤ t := Nat.le_of_not_gt ht
      have hfalse : Bitstream.box (LetterlessFormula.eval p.toFormula) t = false := by
        have hstay := Bitstream.box_stays_false hnfalse (t - n)
        simpa [Nat.add_sub_of_le hge] using hstay
      have hge' :
          (firstFalseOfNotAllTrue (LetterlessFormula.eval p.toFormula) hall).idx ≤ t := by
        simpa [ff, n] using hge
      rw [NormalForm.toFormula, LetterlessFormula.eval_finiteNormalForm]
      simp [List.mem_range, hge', hfalse]

/--
The explicit normal-form box leaves `⊤` unchanged.
-/
theorem NormalForm.box_top :
    NormalForm.box (NormalForm.cofinite []) = NormalForm.cofinite [] := by
  classical
  have hall : ∀ t,
      Bitstream.box (LetterlessFormula.eval (NormalForm.cofinite []).toFormula) t = true := by
    intro t
    simpa [NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm,
      LetterlessFormula.eval_neg, LetterlessFormula.eval_finiteNormalForm, const0, const, const1]
      using congrArg (fun f => f t) box_const1
  simp [NormalForm.box, hall]

/--
Semantically, boxing the initial-segment normal form on `range n` yields the
next initial segment.
-/
theorem NormalForm.eval_box_finite_range (n : Nat) :
    LetterlessFormula.eval (NormalForm.box (NormalForm.finite (List.range n))).toFormula =
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := by
  rw [NormalForm.eval_box]
  simp [NormalForm.toFormula]
  have hr :
      LetterlessFormula.eval (LetterlessFormula.finiteNormalForm (List.range n)) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
    simpa [NormalForm.toFormula] using (eval_finite_range n)
  rw [hr]
  simp [LetterlessFormula.eval_box, LetterlessFormula.iterBoxBottom]

/--
The first false time for the boxed initial-segment normal form is exactly
`n + 1`.
-/
theorem first_false_finite_range_unique (n m : Nat)
    (hmfalse :
      Bitstream.box (LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula) m = false)
    (hmbefore :
      ∀ k, k < m →
        Bitstream.box (LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula) k = true) :
    m = n + 1 := by
  have hsem :
      Bitstream.box (LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := by
    exact Eq.trans (NormalForm.eval_box (NormalForm.finite (List.range n))).symm
      (NormalForm.eval_box_finite_range n)
  have hmfalse' :
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) m = false := by
    simpa [hsem] using hmfalse
  have hnotlt : ¬ m < n + 1 := by
    intro hlt
    have htrue :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) m = true :=
      (LetterlessFormula.eval_iterBoxBottom_true_iff (n + 1) m).2 hlt
    simp [htrue] at hmfalse'
  have hle : n + 1 ≤ m := Nat.le_of_not_gt hnotlt
  have hge : m ≤ n + 1 := by
    by_cases hlt : n + 1 < m
    · have htrue :
          Bitstream.box (LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula) (n + 1) = true :=
        hmbefore (n + 1) hlt
      have hfalse :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) (n + 1) = false := by
        have hnot : ¬ (n + 1) < n + 1 := Nat.lt_irrefl (n + 1)
        cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) (n + 1) with
        | false => exact rfl
        | true =>
            exact False.elim (hnot ((LetterlessFormula.eval_iterBoxBottom_true_iff (n + 1) (n + 1)).1 hval))
      have htrue' :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) (n + 1) = true := by
        simpa [hsem] using htrue
      simp [hfalse] at htrue'
    · exact Nat.le_of_not_gt hlt
  exact Nat.le_antisymm hge hle

/--
Boxing the initial-segment normal form on `range n` yields the next initial
segment as a normal form.
-/
theorem NormalForm.box_finite_range (n : Nat) :
    NormalForm.box (NormalForm.finite (List.range n)) =
      NormalForm.finite (List.range (n + 1)) := by
  classical
  have hnotall :
      ¬ ∀ t,
        Bitstream.box (LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula) t = true := by
    intro hall
    have hfalse :
        Bitstream.box (LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula) (n + 1) = false := by
      have hsem :
          Bitstream.box (LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula) =
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := by
        exact Eq.trans (NormalForm.eval_box (NormalForm.finite (List.range n))).symm
          (NormalForm.eval_box_finite_range n)
      have hnot : ¬ (n + 1) < n + 1 := Nat.lt_irrefl (n + 1)
      cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) (n + 1) with
      | false =>
          simpa [hsem] using hval
      | true =>
          exact False.elim (hnot ((LetterlessFormula.eval_iterBoxBottom_true_iff (n + 1) (n + 1)).1 hval))
    have htrue := hall (n + 1)
    simp [hfalse] at htrue
  let ff : FirstFalse
      (Bitstream.box (LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula)) :=
    firstFalseOfNotAllTrue
      (LetterlessFormula.eval (NormalForm.finite (List.range n)).toFormula) hnotall
  let m : Nat := ff.idx
  have hm' : m = ff.idx := rfl
  have hm :
      m = n + 1 :=
    first_false_finite_range_unique n m
      ff.false_at ff.before_true
  simp [NormalForm.box, hnotall, ff, m, hm]

/--
Syntax-directed normalization into a Boolos-style normal form. This is
noncomputable because the underlying normal-form operations still re-normalize
via eventual constancy, but it is now genuinely recursive on the syntax.
-/
noncomputable def normalize : LetterlessFormula → NormalForm
  | ⊥ => NormalForm.finite []
  | a ⇒ b => NormalForm.imp (normalize a) (normalize b)
  | □a => NormalForm.box (normalize a)

/--
Semantic correctness of the syntax-directed normalization.
-/
theorem eval_normalize : ∀ a : LetterlessFormula,
    LetterlessFormula.eval (normalize a).toFormula = LetterlessFormula.eval a
  | ⊥ => by
      rfl
  | a ⇒ b => by
      simp [normalize, LetterlessFormula.eval_imp, NormalForm.eval_imp, eval_normalize a,
        eval_normalize b]
  | □a => by
      simp [normalize, LetterlessFormula.eval_box, NormalForm.eval_box, eval_normalize a]

/--
Once the normal-form operations for implication and box are proved
proof-theoretically correct, the recursive normalizer yields a provably
equivalent normal form for every letterless formula.
-/
theorem eqv_normalize_of_ops
    (himp : ∀ p q : NormalForm,
      Provable.Eqv (NormalForm.imp p q).toFormula (p.toFormula ⇒ q.toFormula))
    (hbox : ∀ p : NormalForm,
      Provable.Eqv (p.box).toFormula (□(p.toFormula))) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a
  | ⊥ => by
      exact Provable.eqv_refl _
  | a ⇒ b => by
      have ha : Provable.Eqv (normalize a).toFormula a := eqv_normalize_of_ops himp hbox a
      have hb : Provable.Eqv (normalize b).toFormula b := eqv_normalize_of_ops himp hbox b
      have hstep :
          Provable.Eqv (normalize (a ⇒ b)).toFormula
            ((normalize a).toFormula ⇒ (normalize b).toFormula) :=
        himp (normalize a) (normalize b)
      exact Provable.eqv_trans hstep (Provable.eqv_imp ha hb)
  | □a => by
      have ha : Provable.Eqv (normalize a).toFormula a := eqv_normalize_of_ops himp hbox a
      have hstep : Provable.Eqv (normalize (□a)).toFormula (□((normalize a).toFormula)) :=
        hbox (normalize a)
      exact Provable.eqv_trans hstep (Provable.eqv_box ha)

/--
Proof-theoretic correctness of explicit normal-form implication reduces to the
four concrete finite/cofinite cases.
-/
theorem eqv_imp_of_cases
    (hff : ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula
        ((NormalForm.finite xs).toFormula ⇒ (NormalForm.finite ys).toFormula))
    (hfc : ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.finite xs) (NormalForm.cofinite ys)).toFormula
        ((NormalForm.finite xs).toFormula ⇒ (NormalForm.cofinite ys).toFormula))
    (hcf : ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.cofinite xs) (NormalForm.finite ys)).toFormula
        ((NormalForm.cofinite xs).toFormula ⇒ (NormalForm.finite ys).toFormula))
    (hcc : ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.cofinite xs) (NormalForm.cofinite ys)).toFormula
        ((NormalForm.cofinite xs).toFormula ⇒ (NormalForm.cofinite ys).toFormula)) :
    ∀ p q : NormalForm,
      Provable.Eqv (NormalForm.imp p q).toFormula (p.toFormula ⇒ q.toFormula)
  | NormalForm.finite xs, NormalForm.finite ys => hff xs ys
  | NormalForm.finite xs, NormalForm.cofinite ys => hfc xs ys
  | NormalForm.cofinite xs, NormalForm.finite ys => hcf xs ys
  | NormalForm.cofinite xs, NormalForm.cofinite ys => hcc xs ys

/--
The `cofinite → finite` implication case reduces to closure of finite normal
forms under disjunction.
-/
theorem eqv_imp_cofinite_finite_of_append
    (happend : ∀ xs ys : List Nat,
      Provable.Eqv (LetterlessFormula.disj
            (LetterlessFormula.finiteNormalForm xs)
            (LetterlessFormula.finiteNormalForm ys))
          (LetterlessFormula.finiteNormalForm (xs ++ ys))) :
    ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.cofinite xs) (NormalForm.finite ys)).toFormula
        ((NormalForm.cofinite xs).toFormula ⇒ (NormalForm.finite ys).toFormula)
  | xs, ys => by
      simpa [NormalForm.imp, NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm]
        using Provable.eqv_symm (happend xs ys)

/--
Finite normal forms are closed under disjunction by list append.
-/
theorem eqv_disj_finiteNormalForm_append :
    ∀ xs ys : List Nat,
      Provable.Eqv
        (LetterlessFormula.disj
          (LetterlessFormula.finiteNormalForm xs)
          (LetterlessFormula.finiteNormalForm ys))
        (LetterlessFormula.finiteNormalForm (xs ++ ys))
  | [], ys => by
      simpa [LetterlessFormula.finiteNormalForm] using
        (Provable.eqv_bottom_disj (LetterlessFormula.finiteNormalForm ys))
  | x :: xs, ys => by
      have hassoc :
          Provable.Eqv
            (LetterlessFormula.disj
              (LetterlessFormula.disj (LetterlessFormula.pulseAt x)
                (LetterlessFormula.finiteNormalForm xs))
              (LetterlessFormula.finiteNormalForm ys))
            (LetterlessFormula.disj
              (LetterlessFormula.pulseAt x)
              (LetterlessFormula.disj
                (LetterlessFormula.finiteNormalForm xs)
                (LetterlessFormula.finiteNormalForm ys))) :=
        Provable.eqv_disj_assoc
          (LetterlessFormula.pulseAt x)
          (LetterlessFormula.finiteNormalForm xs)
          (LetterlessFormula.finiteNormalForm ys)
      have htail :
          Provable.Eqv
            (LetterlessFormula.disj
              (LetterlessFormula.finiteNormalForm xs)
              (LetterlessFormula.finiteNormalForm ys))
            (LetterlessFormula.finiteNormalForm (xs ++ ys)) :=
        eqv_disj_finiteNormalForm_append xs ys
      have hmap :
          Provable.Eqv
            (LetterlessFormula.disj
              (LetterlessFormula.pulseAt x)
              (LetterlessFormula.disj
                (LetterlessFormula.finiteNormalForm xs)
                (LetterlessFormula.finiteNormalForm ys)))
            (LetterlessFormula.disj
              (LetterlessFormula.pulseAt x)
              (LetterlessFormula.finiteNormalForm (xs ++ ys))) :=
        Provable.eqv_disj (Provable.eqv_refl _) htail
      exact Provable.eqv_trans hassoc <|
        by simpa [LetterlessFormula.finiteNormalForm]
          using hmap

/--
The `cofinite → finite` implication case.
-/
theorem eqv_imp_cofinite_finite :
    ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.cofinite xs) (NormalForm.finite ys)).toFormula
        ((NormalForm.cofinite xs).toFormula ⇒ (NormalForm.finite ys).toFormula) :=
  eqv_imp_cofinite_finite_of_append eqv_disj_finiteNormalForm_append

/--
The `cofinite → cofinite` implication case reduces by contraposition to the
`finite → finite` case.
-/
theorem eqv_imp_cofinite_cofinite_of_finite
    (hfinite : ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula
        ((NormalForm.finite xs).toFormula ⇒ (NormalForm.finite ys).toFormula)) :
    ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.cofinite xs) (NormalForm.cofinite ys)).toFormula
        ((NormalForm.cofinite xs).toFormula ⇒ (NormalForm.cofinite ys).toFormula)
  | xs, ys => by
      have h₁ :
          Provable.Eqv
            (NormalForm.imp (NormalForm.cofinite xs) (NormalForm.cofinite ys)).toFormula
            (NormalForm.imp (NormalForm.finite ys) (NormalForm.finite xs)).toFormula := by
        exact Provable.eqv_refl _
      have h₂ :
          Provable.Eqv
            (NormalForm.imp (NormalForm.finite ys) (NormalForm.finite xs)).toFormula
            ((NormalForm.finite ys).toFormula ⇒ (NormalForm.finite xs).toFormula) :=
        hfinite ys xs
      have h₃ :
          Provable.Eqv
            ((NormalForm.finite ys).toFormula ⇒ (NormalForm.finite xs).toFormula)
            ((NormalForm.cofinite xs).toFormula ⇒ (NormalForm.cofinite ys).toFormula) := by
        simpa [NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm]
          using (Provable.eqv_symm
            (Provable.eqv_contrapositive
              (LetterlessFormula.finiteNormalForm xs)
              (LetterlessFormula.finiteNormalForm ys)))
      exact Provable.eqv_trans h₁ (Provable.eqv_trans h₂ h₃)

/--
Negating a cofinite normal form recovers the corresponding finite normal form.
-/
theorem eqv_neg_cofiniteNormalForm (ns : List Nat) :
    Provable.Eqv (LetterlessFormula.neg (LetterlessFormula.cofiniteNormalForm ns))
      (LetterlessFormula.finiteNormalForm ns) := by
  simpa [LetterlessFormula.cofiniteNormalForm] using
    (Provable.eqv_symm (Provable.eqv_doubleNeg (LetterlessFormula.finiteNormalForm ns)))

/--
Classical equivalence `¬(a ⇒ b) ↔ (a &&& ¬b)`.
-/
theorem eqv_neg_imp_as_conj (a b : LetterlessFormula) :
    Provable.Eqv (LetterlessFormula.neg (a ⇒ b))
      (LetterlessFormula.conj a (LetterlessFormula.neg b)) := by
  have h₁ :
      Provable.Eqv
        (LetterlessFormula.conj (LetterlessFormula.neg (LetterlessFormula.neg a))
          (LetterlessFormula.neg b))
        (LetterlessFormula.neg (LetterlessFormula.disj (LetterlessFormula.neg a) b)) :=
    Provable.eqv_conj_neg_neg (LetterlessFormula.neg a) b
  have h₂ :
      Provable.Eqv
        (LetterlessFormula.conj (LetterlessFormula.neg (LetterlessFormula.neg a))
          (LetterlessFormula.neg b))
        (LetterlessFormula.conj a (LetterlessFormula.neg b)) :=
    Provable.eqv_conj (Provable.eqv_symm (Provable.eqv_doubleNeg a)) (Provable.eqv_refl _)
  have h₃ :
      Provable.Eqv (LetterlessFormula.disj (LetterlessFormula.neg a) b) (a ⇒ b) := by
    simpa [LetterlessFormula.disj, LetterlessFormula.neg] using
      (Provable.eqv_imp (Provable.eqv_symm (Provable.eqv_doubleNeg a)) (Provable.eqv_refl b))
  have h₄ :
      Provable.Eqv
        (LetterlessFormula.neg (LetterlessFormula.disj (LetterlessFormula.neg a) b))
        (LetterlessFormula.neg (a ⇒ b)) :=
    Provable.eqv_neg h₃
  exact Provable.eqv_trans (Provable.eqv_symm h₄)
    (Provable.eqv_trans (Provable.eqv_symm h₁) h₂)

/--
A pulse is exactly the singleton finite normal form at that time.
-/
theorem eqv_pulseAt_singleton (n : Nat) :
    Provable.Eqv (LetterlessFormula.pulseAt n)
      (LetterlessFormula.finiteNormalForm [n]) := by
  have h₁ :
      Provable.Eqv (LetterlessFormula.adjacentClause n)
        (LetterlessFormula.cofiniteNormalForm [n]) :=
    Provable.eqv_adjacentClause_singleHole n
  have h₂ :
      Provable.Eqv (LetterlessFormula.neg (LetterlessFormula.adjacentClause n))
        (LetterlessFormula.neg (LetterlessFormula.cofiniteNormalForm [n])) :=
    Provable.eqv_neg h₁
  have h₃ :
      Provable.Eqv (LetterlessFormula.neg (LetterlessFormula.cofiniteNormalForm [n]))
        (LetterlessFormula.finiteNormalForm [n]) :=
    eqv_neg_cofiniteNormalForm [n]
  exact Provable.eqv_trans (by
    simpa [LetterlessFormula.adjacentClause, LetterlessFormula.neg, iterClause, LetterlessFormula.pulseAt]
      using h₂) h₃

/--
Conjoining a pulse with itself yields the same pulse.
-/
theorem eqv_conj_pulse_same (n : Nat) :
    Provable.Eqv
      (LetterlessFormula.conj (LetterlessFormula.pulseAt n) (LetterlessFormula.pulseAt n))
      (LetterlessFormula.pulseAt n) :=
  Provable.eqv_conj_idem (LetterlessFormula.pulseAt n)

/--
`pulseAt n` is the conjunction of the next larger initial segment with the
negation of the current one.
-/
theorem eqv_pulseAt_as_conj_iter (n : Nat) :
    Provable.Eqv (LetterlessFormula.pulseAt n)
      (LetterlessFormula.conj
        (LetterlessFormula.iterBoxBottom (n + 1))
        (LetterlessFormula.neg (LetterlessFormula.iterBoxBottom n))) := by
  simpa [LetterlessFormula.pulseAt, LetterlessFormula.adjacentClause, iterClause]
    using (eqv_neg_imp_as_conj
      (LetterlessFormula.iterBoxBottom (n + 1))
      (LetterlessFormula.iterBoxBottom n))

/--
Excluded middle in the derived disjunction notation.
-/
theorem provable_em (a : LetterlessFormula) :
    Provable (LetterlessFormula.disj (LetterlessFormula.neg a) a) := by
  simpa [LetterlessFormula.disj, LetterlessFormula.neg] using
    Provable.axiomClassical a

/--
If `b ⇒ a`, then `b ∨ (a ∧ ¬b)` is provably equivalent to `a`.
-/
theorem eqv_disj_conj_neg_of_imp (a b : LetterlessFormula)
    (hba : Provable (b ⇒ a)) :
    Provable.Eqv
      (LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b)))
      a := by
  constructor
  · exact Provable.disj_elim hba (Provable.conj_elim_left _ _)
  · have hcaseNeg :
        Provable (LetterlessFormula.neg b ⇒
          (a ⇒ LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b)))) := by
      have hconj :
          Provable (LetterlessFormula.neg b ⇒
            (a ⇒ LetterlessFormula.conj a (LetterlessFormula.neg b))) := by
        exact Provable.modusPonens
          (Provable.imp_swap a (LetterlessFormula.neg b)
            (LetterlessFormula.conj a (LetterlessFormula.neg b)))
          (Provable.conj_intro_curried a (LetterlessFormula.neg b))
      have hpost :
          Provable
            ((a ⇒ LetterlessFormula.conj a (LetterlessFormula.neg b)) ⇒
              (a ⇒ LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b)))) := by
        have hraw :
            Provable
              ((LetterlessFormula.conj a (LetterlessFormula.neg b) ⇒
                  LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b))) ⇒
                ((a ⇒ LetterlessFormula.conj a (LetterlessFormula.neg b)) ⇒
                  (a ⇒ LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b))))) :=
          Provable.imp_compose a
            (LetterlessFormula.conj a (LetterlessFormula.neg b))
            (LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b)))
        exact Provable.modusPonens hraw
          (Provable.disj_intro_right b (LetterlessFormula.conj a (LetterlessFormula.neg b)))
      have hstep :
          Provable
            (((a ⇒ LetterlessFormula.conj a (LetterlessFormula.neg b)) ⇒
                (a ⇒ LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b)))) ⇒
              (LetterlessFormula.neg b ⇒
                (a ⇒ LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b))))) :=
        Provable.imp_postcompose hconj
      exact Provable.modusPonens hstep hpost
    have hcasePos :
        Provable (b ⇒
          (a ⇒ LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b)))) := by
      exact Provable.modusPonens
        (Provable.imp_swap a b
          (LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b))))
        (Provable.weaken (a := a)
          (Provable.disj_intro_left b (LetterlessFormula.conj a (LetterlessFormula.neg b))))
    have hem :
        Provable (LetterlessFormula.disj (LetterlessFormula.neg b) b) :=
      provable_em b
    have hsplit :
        Provable
          (LetterlessFormula.disj (LetterlessFormula.neg b) b ⇒
            (a ⇒ LetterlessFormula.disj b (LetterlessFormula.conj a (LetterlessFormula.neg b)))) :=
      Provable.disj_elim hcaseNeg hcasePos
    exact Provable.modusPonens hsplit hem

/--
`iterBoxBottom n ∨ pulseAt n` collapses to `iterBoxBottom (n+1)`.
-/
theorem eqv_disj_iterBoxBottom_pulseAt (n : Nat) :
    Provable.Eqv
      (LetterlessFormula.disj
        (LetterlessFormula.iterBoxBottom n)
        (LetterlessFormula.pulseAt n))
      (LetterlessFormula.iterBoxBottom (n + 1)) := by
  have hpulse :
      Provable.Eqv
        (LetterlessFormula.pulseAt n)
        (LetterlessFormula.conj
          (LetterlessFormula.iterBoxBottom (n + 1))
          (LetterlessFormula.neg (LetterlessFormula.iterBoxBottom n))) :=
    eqv_pulseAt_as_conj_iter n
  have hdisj :
      Provable.Eqv
        (LetterlessFormula.disj
          (LetterlessFormula.iterBoxBottom n)
          (LetterlessFormula.pulseAt n))
        (LetterlessFormula.disj
          (LetterlessFormula.iterBoxBottom n)
          (LetterlessFormula.conj
            (LetterlessFormula.iterBoxBottom (n + 1))
            (LetterlessFormula.neg (LetterlessFormula.iterBoxBottom n)))) :=
    Provable.eqv_disj (Provable.eqv_refl _) hpulse
  have hcollapse :
      Provable.Eqv
        (LetterlessFormula.disj
          (LetterlessFormula.iterBoxBottom n)
          (LetterlessFormula.conj
            (LetterlessFormula.iterBoxBottom (n + 1))
            (LetterlessFormula.neg (LetterlessFormula.iterBoxBottom n))))
        (LetterlessFormula.iterBoxBottom (n + 1)) :=
    eqv_disj_conj_neg_of_imp
      (LetterlessFormula.iterBoxBottom (n + 1))
      (LetterlessFormula.iterBoxBottom n)
      (provable_iterBoxBottom_step n)
  exact Provable.eqv_trans hdisj hcollapse

/--
The finite normal form on `range n` is provably equivalent to `iterBoxBottom n`.
-/
theorem eqv_finite_range_iterBoxBottom :
    ∀ n : Nat,
      Provable.Eqv
        (LetterlessFormula.finiteNormalForm (List.range n))
        (LetterlessFormula.iterBoxBottom n)
  | 0 => by
      simpa [LetterlessFormula.finiteNormalForm, LetterlessFormula.iterBoxBottom]
        using (Provable.eqv_refl ⊥)
  | n + 1 => by
      have happend :
          Provable.Eqv
            (LetterlessFormula.disj
              (LetterlessFormula.finiteNormalForm (List.range n))
              (LetterlessFormula.finiteNormalForm [n]))
            (LetterlessFormula.finiteNormalForm (List.range n ++ [n])) := by
        simpa using
          (eqv_disj_finiteNormalForm_append (List.range n) [n])
      have hsplit :
          Provable.Eqv
            (LetterlessFormula.finiteNormalForm (List.range (n + 1)))
            (LetterlessFormula.disj
              (LetterlessFormula.finiteNormalForm (List.range n))
              (LetterlessFormula.finiteNormalForm [n])) := by
        simpa [List.range_succ] using Provable.eqv_symm happend
      have hpulse :
          Provable.Eqv
            (LetterlessFormula.disj
              (LetterlessFormula.finiteNormalForm (List.range n))
              (LetterlessFormula.finiteNormalForm [n]))
            (LetterlessFormula.disj
              (LetterlessFormula.finiteNormalForm (List.range n))
              (LetterlessFormula.pulseAt n)) :=
        Provable.eqv_disj (Provable.eqv_refl _)
          (Provable.eqv_symm (eqv_pulseAt_singleton n))
      have htail :
          Provable.Eqv
            (LetterlessFormula.disj
              (LetterlessFormula.finiteNormalForm (List.range n))
              (LetterlessFormula.pulseAt n))
            (LetterlessFormula.disj
              (LetterlessFormula.iterBoxBottom n)
              (LetterlessFormula.pulseAt n)) :=
        Provable.eqv_disj (eqv_finite_range_iterBoxBottom n) (Provable.eqv_refl _)
      exact Provable.eqv_trans hsplit <|
        Provable.eqv_trans hpulse <|
          Provable.eqv_trans htail
            (eqv_disj_iterBoxBottom_pulseAt n)

/--
The empty cofinite normal form is just `⊤`.
-/
theorem eqv_cofinite_nil_top :
    Provable.Eqv (NormalForm.cofinite []).toFormula LetterlessFormula.top := by
  simpa [NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm,
    LetterlessFormula.finiteNormalForm, LetterlessFormula.neg, LetterlessFormula.top]
    using (Provable.eqv_refl LetterlessFormula.top)

/--
Proof-theoretic correctness of normal-form box at `⊤`.
-/
theorem eqv_box_top_normalForm :
    Provable.Eqv (NormalForm.box (NormalForm.cofinite [])).toFormula
      (□((NormalForm.cofinite []).toFormula)) := by
  rw [NormalForm.box_top]
  exact Provable.eqv_trans eqv_cofinite_nil_top <|
    Provable.eqv_trans
      (Provable.eqv_symm eqv_box_top)
      (Provable.eqv_symm (Provable.eqv_box eqv_cofinite_nil_top))

/--
Proof-theoretic correctness of normal-form box on the initial-segment normal
forms `range n`.
-/
theorem eqv_box_finite_range_normalForm (n : Nat) :
    Provable.Eqv (NormalForm.box (NormalForm.finite (List.range n))).toFormula
      (□((NormalForm.finite (List.range n)).toFormula)) := by
  rw [NormalForm.box_finite_range]
  have hleft :
      Provable.Eqv
        (NormalForm.finite (List.range (n + 1))).toFormula
        (LetterlessFormula.iterBoxBottom (n + 1)) :=
    eqv_finite_range_iterBoxBottom (n + 1)
  have hright :
      Provable.Eqv
        (□((NormalForm.finite (List.range n)).toFormula))
        (LetterlessFormula.iterBoxBottom (n + 1)) :=
    Provable.eqv_trans
      (Provable.eqv_box (eqv_finite_range_iterBoxBottom n))
      (eqv_box_iterBoxBottom n)
  exact Provable.eqv_trans hleft (Provable.eqv_symm hright)

/--
Boxing the finite normal form on `range n` yields `□^(n+1) ⊥`.
-/
theorem eqv_box_formula_finite_range (n : Nat) :
    Provable.Eqv
      (□((NormalForm.finite (List.range n)).toFormula))
      (LetterlessFormula.iterBoxBottom (n + 1)) := by
  exact Provable.eqv_trans
    (Provable.eqv_symm (eqv_box_finite_range_normalForm n))
    (by
      rw [NormalForm.box_finite_range]
      exact eqv_finite_range_iterBoxBottom (n + 1))

/--
Boxing the empty cofinite normal form yields `⊤`.
-/
theorem eqv_box_formula_cofinite_nil :
    Provable.Eqv
      (□((NormalForm.cofinite []).toFormula))
      LetterlessFormula.top := by
  exact Provable.eqv_trans
    (Provable.eqv_symm eqv_box_top_normalForm)
    (by
      rw [NormalForm.box_top]
      exact eqv_cofinite_nil_top)

/--
Every explicit normal-form box is provably equivalent either to `⊤` or to an
iterated bottom `□^n ⊥`.
-/
theorem eqv_box_normalForm_shape (p : NormalForm) :
    ∃ q : LetterlessFormula,
      Provable.Eqv (p.box).toFormula q ∧
        (q = LetterlessFormula.top ∨ ∃ n, q = LetterlessFormula.iterBoxBottom n) := by
  classical
  by_cases hall : ∀ t, Bitstream.box (LetterlessFormula.eval p.toFormula) t = true
  · refine ⟨LetterlessFormula.top, ?_, Or.inl rfl⟩
    have hboxeq : p.box = NormalForm.cofinite [] := by
      simp [NormalForm.box, hall]
    rw [hboxeq]
    exact eqv_cofinite_nil_top
  · let ff : FirstFalse (Bitstream.box (LetterlessFormula.eval p.toFormula)) :=
      firstFalseOfNotAllTrue (LetterlessFormula.eval p.toFormula) hall
    let n : Nat := ff.idx
    have hn : n = ff.idx := rfl
    refine ⟨LetterlessFormula.iterBoxBottom n, ?_, Or.inr ⟨n, rfl⟩⟩
    have hboxeq : p.box = NormalForm.finite (List.range n) := by
      simp [NormalForm.box, hall, ff, n]
    rw [hboxeq]
    exact eqv_finite_range_iterBoxBottom n

/--
The boxed denotation of any normal form has a canonical representative which is
provably equivalent to the chosen normal-form box and semantically identical to
`□(p.toFormula)`.
-/
theorem exists_canonical_box_representative (p : NormalForm) :
    ∃ q : LetterlessFormula,
      Provable.Eqv (p.box).toFormula q ∧
      LetterlessFormula.eval q = LetterlessFormula.eval (□(p.toFormula)) ∧
      (q = LetterlessFormula.top ∨ ∃ n, q = LetterlessFormula.iterBoxBottom n) := by
  rcases eqv_box_normalForm_shape p with ⟨q, hq, hshape⟩
  refine ⟨q, hq, ?_, hshape⟩
  have hqq : LetterlessFormula.eval q = LetterlessFormula.eval (p.box).toFormula := by
    exact (Provable.eqv_sound hq).symm
  calc
    LetterlessFormula.eval q = LetterlessFormula.eval (p.box).toFormula := hqq
    _ = Bitstream.box (LetterlessFormula.eval p.toFormula) := NormalForm.eval_box p
    _ = LetterlessFormula.eval (□(p.toFormula)) := by rfl

/--
A natural number strictly above every element of a finite list.
-/
def succAbove (xs : List Nat) : Nat :=
  xs.foldr Nat.max 0 + 1

/--
Minimum of a nonempty list, computed recursively.
-/
def minList : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: xs => Nat.min x (minList (y :: xs))

theorem minList_mem_of_ne_nil {xs : List Nat} (hxs : xs ≠ []) :
    minList xs ∈ xs := by
  induction xs with
  | nil =>
      contradiction
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [minList]
      | cons y ys =>
          simp [minList]
          by_cases hxy : x ≤ minList (y :: ys)
          · exact Or.inl (Nat.min_eq_left hxy)
          · have hmem : minList (y :: ys) ∈ y :: ys := ih (by simp)
            have hmin :
                Nat.min x (minList (y :: ys)) ∈ y :: ys := by
              simpa [Nat.min_eq_right (Nat.le_of_not_ge hxy)] using hmem
            exact Or.inr (by simpa using hmin)

theorem minList_le_of_mem {xs : List Nat} (hxs : xs ≠ []) {x : Nat} (hx : x ∈ xs) :
    minList xs ≤ x := by
  induction xs with
  | nil =>
      contradiction
  | cons a xs ih =>
      cases xs with
      | nil =>
          simp at hx
          simp [minList, hx]
      | cons b ys =>
          simp at hx ⊢
          cases hx with
          | inl hax =>
              simpa [hax] using Nat.min_le_left a (minList (b :: ys))
          | inr hrest =>
              have hmem : x ∈ b :: ys := by
                simpa using hrest
              exact Nat.le_trans (Nat.min_le_right a (minList (b :: ys)))
                (ih (by simp) hmem)

theorem not_mem_of_lt_minList {xs : List Nat} (hxs : xs ≠ []) {x : Nat}
    (hx : x < minList xs) :
    x ∉ xs := by
  intro hmem
  exact Nat.not_lt_of_ge (minList_le_of_mem hxs hmem) hx

theorem lt_succAbove_of_mem {xs : List Nat} {x : Nat} (hx : x ∈ xs) :
    x < succAbove xs := by
  induction xs with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp [succAbove] at hx ⊢
      rcases hx with rfl | hx
      · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
      · have hxle : x ≤ List.foldr Nat.max 0 ys := Nat.le_of_lt_succ (ih hx)
        exact Nat.lt_succ_of_le (Nat.le_trans hxle (Nat.le_max_right _ _))

theorem not_mem_succAbove (xs : List Nat) :
    succAbove xs ∉ xs := by
  intro hmem
  exact Nat.lt_irrefl _ (lt_succAbove_of_mem hmem)

/--
The boxed denotation of a finite normal form is never constantly true.
-/
theorem finite_box_not_all_true (xs : List Nat) :
    ¬ ∀ t, Bitstream.box (LetterlessFormula.eval (NormalForm.finite xs).toFormula) t = true := by
  intro hall
  have hsfalse :
      LetterlessFormula.eval (NormalForm.finite xs).toFormula (succAbove xs) = false := by
    rw [NormalForm.toFormula, LetterlessFormula.eval_finiteNormalForm]
    simp [not_mem_succAbove]
  have hboxfalse :
      Bitstream.box (LetterlessFormula.eval (NormalForm.finite xs).toFormula) (succAbove xs + 1) = false :=
    Bitstream.box_succ_of_input_false hsfalse
  have htrue := hall (succAbove xs + 1)
  simp [hboxfalse] at htrue

/--
For every finite normal form, the boxed formula has an iterated-bottom
canonical representative.
-/
theorem exists_finite_box_iterBoxBottom (xs : List Nat) :
    ∃ n,
      Provable.Eqv (NormalForm.box (NormalForm.finite xs)).toFormula
        (LetterlessFormula.iterBoxBottom n) ∧
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
        LetterlessFormula.eval (□((NormalForm.finite xs).toFormula)) := by
  rcases exists_canonical_box_representative (NormalForm.finite xs) with
    ⟨q, hq, heval, hshape⟩
  cases hshape with
  | inl htop =>
      exfalso
      have hall :
          ∀ t, Bitstream.box (LetterlessFormula.eval (NormalForm.finite xs).toFormula) t = true := by
        intro t
        have hconst :
            LetterlessFormula.eval (□((NormalForm.finite xs).toFormula)) = const1 := by
          simpa [htop, LetterlessFormula.eval_top] using heval.symm
        simpa [LetterlessFormula.eval_box, const1, const] using congrArg (fun f => f t) hconst
      exact finite_box_not_all_true xs hall
  | inr hiter =>
      rcases hiter with ⟨n, rfl⟩
      exact ⟨n, hq, heval⟩

/--
Boxing a finite normal form yields an initial-segment normal form.
-/
theorem exists_box_finite_range (xs : List Nat) :
    ∃ n, NormalForm.box (NormalForm.finite xs) = NormalForm.finite (List.range n) := by
  classical
  have hnotall := finite_box_not_all_true xs
  let ff : FirstFalse (Bitstream.box (LetterlessFormula.eval (NormalForm.finite xs).toFormula)) :=
    firstFalseOfNotAllTrue
      (LetterlessFormula.eval (NormalForm.finite xs).toFormula) hnotall
  let n : Nat := ff.idx
  have hn : n = ff.idx := rfl
  refine ⟨n, ?_⟩
  simp [NormalForm.box, hnotall, ff, n]

/--
Proof-theoretically, the box of a finite normal form is an iterated bottom.
-/
theorem exists_eqv_box_finite_iterBoxBottom (xs : List Nat) :
    ∃ n,
      Provable.Eqv (NormalForm.box (NormalForm.finite xs)).toFormula
        (LetterlessFormula.iterBoxBottom n) := by
  rcases exists_box_finite_range xs with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [hn]
  exact eqv_finite_range_iterBoxBottom n

/--
Boxing a nonempty cofinite normal form yields the initial segment determined by
its least hole.
-/
theorem NormalForm.box_cofinite_ne_nil (xs : List Nat) (hxs : xs ≠ []) :
    NormalForm.box (NormalForm.cofinite xs) =
      NormalForm.finite (List.range (minList xs + 1)) := by
  classical
  have hinputFalse :
      LetterlessFormula.eval (NormalForm.cofinite xs).toFormula (minList xs) = false := by
    rw [NormalForm.toFormula, LetterlessFormula.eval_cofiniteNormalForm]
    simp [minList_mem_of_ne_nil hxs]
  have hnotall :
      ¬ ∀ t, Bitstream.box (LetterlessFormula.eval (NormalForm.cofinite xs).toFormula) t = true := by
    intro hall
    have hboxfalse :
        Bitstream.box (LetterlessFormula.eval (NormalForm.cofinite xs).toFormula) (minList xs + 1) = false :=
      Bitstream.box_succ_of_input_false hinputFalse
    have htrue := hall (minList xs + 1)
    simp [hboxfalse] at htrue
  let ff : FirstFalse (Bitstream.box (LetterlessFormula.eval (NormalForm.cofinite xs).toFormula)) :=
    firstFalseOfNotAllTrue
      (LetterlessFormula.eval (NormalForm.cofinite xs).toFormula) hnotall
  let n : Nat := ff.idx
  have hn' : n = ff.idx := rfl
  have hnfalse :
      Bitstream.box (LetterlessFormula.eval (NormalForm.cofinite xs).toFormula) n = false :=
    ff.false_at
  have hnbefore :
      ∀ k, k < n → Bitstream.box (LetterlessFormula.eval (NormalForm.cofinite xs).toFormula) k = true :=
    ff.before_true
  have hmfalse :
      Bitstream.box (LetterlessFormula.eval (NormalForm.cofinite xs).toFormula) (minList xs + 1) = false :=
    Bitstream.box_succ_of_input_false hinputFalse
  have hmbefore :
      ∀ k, k < minList xs + 1 →
        Bitstream.box (LetterlessFormula.eval (NormalForm.cofinite xs).toFormula) k = true := by
    intro k hk
    apply (Bitstream.box_eq_true_iff_prefix_all_true _ k).2
    intro j hj
    have hjlt : j < minList xs := Nat.lt_of_lt_of_le hj (Nat.le_of_lt_succ hk)
    rw [NormalForm.toFormula, LetterlessFormula.eval_cofiniteNormalForm]
    simp [not_mem_of_lt_minList hxs hjlt]
  have hn : n = minList xs + 1 :=
    first_false_unique hnfalse hnbefore hmfalse hmbefore
  simp [NormalForm.box, hnotall, ff, n, hn]

/--
Semantically, boxing a nonempty cofinite normal form yields the initial segment
up to and including its least hole.
-/
theorem eval_box_formula_cofinite_ne_nil (xs : List Nat) (hxs : xs ≠ []) :
    LetterlessFormula.eval (□((NormalForm.cofinite xs).toFormula)) =
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (minList xs + 1)) := by
  rw [LetterlessFormula.eval_box]
  rw [← NormalForm.eval_box (NormalForm.cofinite xs)]
  rw [NormalForm.box_cofinite_ne_nil xs hxs]
  simpa [NormalForm.toFormula] using
    (eval_finite_range (minList xs + 1))

/--
To finish the nonempty cofinite case, it is enough to upgrade the semantic
identification of the boxed formula with the corresponding iterated bottom into
a provable equivalence.
-/
theorem eqv_box_formula_cofinite_ne_nil_of_semantic_bridge
    (hbridge : ∀ xs : List Nat, xs ≠ [] →
      Provable.Eqv
        (□((NormalForm.cofinite xs).toFormula))
        (LetterlessFormula.iterBoxBottom (minList xs + 1))) :
    ∀ xs : List Nat, xs ≠ [] →
      Provable.Eqv
        (NormalForm.box (NormalForm.cofinite xs)).toFormula
        (□((NormalForm.cofinite xs).toFormula))
  | xs, hxs => by
      rw [NormalForm.box_cofinite_ne_nil xs hxs]
      exact Provable.eqv_trans
        (eqv_finite_range_iterBoxBottom (minList xs + 1))
        (Provable.eqv_symm (hbridge xs hxs))


/--
To prove the finite box case, it is enough to show that every boxed finite
normal form is provably equivalent to some iterated bottom.
-/
theorem eqv_box_finite_of_iterBoxBottom
    (hiter : ∀ xs : List Nat, ∃ n,
      Provable.Eqv (□((NormalForm.finite xs).toFormula))
        (LetterlessFormula.iterBoxBottom n)) :
    ∀ xs : List Nat,
      Provable.Eqv (NormalForm.box (NormalForm.finite xs)).toFormula
        (□((NormalForm.finite xs).toFormula))
  | xs => by
      rcases exists_eqv_box_finite_iterBoxBottom xs with ⟨n, hleft⟩
      rcases hiter xs with ⟨m, hright⟩
      have hsemLeft :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
            LetterlessFormula.eval (□((NormalForm.finite xs).toFormula)) := by
        calc
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)
              = LetterlessFormula.eval (NormalForm.box (NormalForm.finite xs)).toFormula :=
            (Provable.eqv_sound hleft).symm
          _ = LetterlessFormula.eval (□((NormalForm.finite xs).toFormula)) := by
            rw [NormalForm.eval_box]
            rfl
      have hsemRight :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) =
            LetterlessFormula.eval (□((NormalForm.finite xs).toFormula)) :=
        (Provable.eqv_sound hright).symm
      have hnm :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) := by
        rw [hsemLeft, hsemRight]
      have hnmEq : n = m := by
        by_cases h : n = m
        · exact h
        · have hltor := Nat.lt_or_gt_of_ne h
          cases hltor with
          | inl hlt =>
              have hntrue :
                  LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) n = true :=
                (LetterlessFormula.eval_iterBoxBottom_true_iff m n).2 hlt
              have hnfalse :
                  LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) n = false := by
                cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) n with
                | false => exact rfl
                | true =>
                    exact False.elim
                      (Nat.lt_irrefl n
                        ((LetterlessFormula.eval_iterBoxBottom_true_iff n n).1 hval))
              have hcontra := congrArg (fun f => f n) hnm
              simp [hntrue, hnfalse] at hcontra
          | inr hgt =>
              have hmtrue :
                  LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) m = true :=
                (LetterlessFormula.eval_iterBoxBottom_true_iff n m).2 hgt
              have hmfalse :
                  LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) m = false := by
                cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) m with
                | false => exact rfl
                | true =>
                    exact False.elim
                      (Nat.lt_irrefl m
                        ((LetterlessFormula.eval_iterBoxBottom_true_iff m m).1 hval))
              have hcontra := congrArg (fun f => f m) hnm
              simp [hmtrue, hmfalse] at hcontra
      exact Provable.eqv_trans hleft (Provable.eqv_symm (hnmEq ▸ hright))

/--
To finish the finite case, it is enough to upgrade the semantic identification
of the boxed formula with some iterated bottom into a provable equivalence.
-/
theorem eqv_box_formula_finite_of_semantic_bridge
    (hbridge : ∀ xs : List Nat, ∃ n,
      Provable.Eqv
        (□((NormalForm.finite xs).toFormula))
        (LetterlessFormula.iterBoxBottom n)) :
    ∀ xs : List Nat,
      Provable.Eqv
        (NormalForm.box (NormalForm.finite xs)).toFormula
        (□((NormalForm.finite xs).toFormula)) :=
  eqv_box_finite_of_iterBoxBottom hbridge

/--
The iterated-bottom family is semantically injective.
-/
theorem eval_iterBoxBottom_injective {n m : Nat}
    (h :
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m)) :
    n = m := by
  by_cases hnm : n = m
  · exact hnm
  · have hltor := Nat.lt_or_gt_of_ne hnm
    cases hltor with
    | inl hlt =>
        have hmtrue :
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) n = true :=
          (LetterlessFormula.eval_iterBoxBottom_true_iff m n).2 hlt
        have hnfalse :
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) n = false := by
          cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) n with
          | false => exact rfl
          | true =>
              exact False.elim
                (Nat.lt_irrefl n
                  ((LetterlessFormula.eval_iterBoxBottom_true_iff n n).1 hval))
        have hcontra := congrArg (fun f => f n) h
        simp [hmtrue, hnfalse] at hcontra
    | inr hgt =>
        have hntrue :
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) m = true :=
          (LetterlessFormula.eval_iterBoxBottom_true_iff n m).2 hgt
        have hmfalse :
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) m = false := by
          cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) m with
          | false => exact rfl
          | true =>
              exact False.elim
                (Nat.lt_irrefl m
                  ((LetterlessFormula.eval_iterBoxBottom_true_iff m m).1 hval))
        have hcontra := congrArg (fun f => f m) h
        simp [hntrue, hmfalse] at hcontra

/--
No iterated-bottom formula is semantically equal to `⊤`.
-/
theorem eval_iterBoxBottom_ne_top (n : Nat) :
    LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) ≠
      LetterlessFormula.eval LetterlessFormula.top := by
  intro h
  have hfalse :
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) n = false := by
    cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) n with
    | false => exact rfl
    | true =>
        exact False.elim
          (Nat.lt_irrefl n
            ((LetterlessFormula.eval_iterBoxBottom_true_iff n n).1 hval))
  have htrue : LetterlessFormula.eval LetterlessFormula.top n = true := by
    simp [LetterlessFormula.eval_top, const1, const]
  have hcontra := congrArg (fun f => f n) h
  simp [hfalse, htrue] at hcontra

/--
To prove the cofinite box case, it is enough to show that every boxed cofinite
normal form is provably equivalent either to `⊤` or to some iterated bottom.
-/
theorem eqv_box_cofinite_of_canonical
    (hcanon : ∀ xs : List Nat,
      Provable.Eqv (□((NormalForm.cofinite xs).toFormula)) LetterlessFormula.top
      ∨ ∃ n, Provable.Eqv (□((NormalForm.cofinite xs).toFormula))
          (LetterlessFormula.iterBoxBottom n)) :
    ∀ xs : List Nat,
      Provable.Eqv (NormalForm.box (NormalForm.cofinite xs)).toFormula
        (□((NormalForm.cofinite xs).toFormula))
  | xs => by
      rcases eqv_box_normalForm_shape (NormalForm.cofinite xs) with ⟨q, hleft, hshape⟩
      rcases hcanon xs with hright | ⟨m, hright⟩
      · cases hshape with
        | inl hq =>
            have hleft' :
                Provable.Eqv (NormalForm.box (NormalForm.cofinite xs)).toFormula
                  LetterlessFormula.top := by
              simpa [hq] using hleft
            exact Provable.eqv_trans hleft' (Provable.eqv_symm hright)
        | inr hq =>
            rcases hq with ⟨n, hq⟩
            exfalso
            have hleft' :
                Provable.Eqv (NormalForm.box (NormalForm.cofinite xs)).toFormula
                  (LetterlessFormula.iterBoxBottom n) := by
              simpa [hq] using hleft
            have hsemLeft :
                LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
                  LetterlessFormula.eval (□((NormalForm.cofinite xs).toFormula)) := by
              calc
                LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)
                    = LetterlessFormula.eval (NormalForm.box (NormalForm.cofinite xs)).toFormula :=
                  (Provable.eqv_sound hleft').symm
                _ = LetterlessFormula.eval (□((NormalForm.cofinite xs).toFormula)) := by
                  rw [NormalForm.eval_box]
                  rfl
            have hsemTop :
                LetterlessFormula.eval LetterlessFormula.top =
                  LetterlessFormula.eval (□((NormalForm.cofinite xs).toFormula)) :=
              (Provable.eqv_sound hright).symm
            exact eval_iterBoxBottom_ne_top n (Eq.trans hsemLeft hsemTop.symm)
      · cases hshape with
        | inl hq =>
            exfalso
            have hleft' :
                Provable.Eqv (NormalForm.box (NormalForm.cofinite xs)).toFormula
                  LetterlessFormula.top := by
              simpa [hq] using hleft
            have hsemTop :
                LetterlessFormula.eval LetterlessFormula.top =
                  LetterlessFormula.eval (□((NormalForm.cofinite xs).toFormula)) := by
              calc
                LetterlessFormula.eval LetterlessFormula.top
                    = LetterlessFormula.eval (NormalForm.box (NormalForm.cofinite xs)).toFormula :=
                  (Provable.eqv_sound hleft').symm
                _ = LetterlessFormula.eval (□((NormalForm.cofinite xs).toFormula)) := by
                  rw [NormalForm.eval_box]
                  rfl
            have hsemRight :
                LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) =
                  LetterlessFormula.eval (□((NormalForm.cofinite xs).toFormula)) :=
              (Provable.eqv_sound hright).symm
            exact eval_iterBoxBottom_ne_top m (Eq.trans hsemRight hsemTop.symm)
        | inr hq =>
            rcases hq with ⟨n, hq⟩
            have hleft' :
                Provable.Eqv (NormalForm.box (NormalForm.cofinite xs)).toFormula
                  (LetterlessFormula.iterBoxBottom n) := by
              simpa [hq] using hleft
            have hnm :
                LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
                  LetterlessFormula.eval (LetterlessFormula.iterBoxBottom m) := by
              have hboxeq :
                  LetterlessFormula.eval (NormalForm.box (NormalForm.cofinite xs)).toFormula =
                    LetterlessFormula.eval (□((NormalForm.cofinite xs).toFormula)) := by
                rw [NormalForm.eval_box]
                rfl
              exact Eq.trans
                (Eq.trans (Provable.eqv_sound hleft').symm hboxeq)
                (Provable.eqv_sound hright)
            exact Provable.eqv_trans hleft'
              (Provable.eqv_symm ((eval_iterBoxBottom_injective hnm) ▸ hright))

/--
Every boxed cofinite normal form is proof-theoretically equivalent either to
`⊤` or to an iterated bottom.
-/
theorem exists_eqv_box_cofinite_canonical (xs : List Nat) :
    Provable.Eqv (NormalForm.box (NormalForm.cofinite xs)).toFormula LetterlessFormula.top
    ∨ ∃ n,
        Provable.Eqv (NormalForm.box (NormalForm.cofinite xs)).toFormula
          (LetterlessFormula.iterBoxBottom n) := by
  by_cases hxs : xs = []
  · left
    rw [hxs, NormalForm.box_top]
    exact eqv_cofinite_nil_top
  · right
    refine ⟨minList xs + 1, ?_⟩
    rw [NormalForm.box_cofinite_ne_nil xs hxs]
    exact eqv_finite_range_iterBoxBottom (minList xs + 1)

/--
Proof-theoretic correctness of normal-form box reduces to the finite and
cofinite cases.
-/
theorem eqv_box_of_cases
    (hfin : ∀ xs : List Nat,
      Provable.Eqv (NormalForm.box (NormalForm.finite xs)).toFormula
        (□((NormalForm.finite xs).toFormula)))
    (hcof : ∀ xs : List Nat,
      Provable.Eqv (NormalForm.box (NormalForm.cofinite xs)).toFormula
        (□((NormalForm.cofinite xs).toFormula))) :
    ∀ p : NormalForm, Provable.Eqv (p.box).toFormula (□(p.toFormula))
  | NormalForm.finite xs => hfin xs
  | NormalForm.cofinite xs => hcof xs

/--
The normal-form box correctness theorem already holds for the canonical cases
we understand explicitly: `⊤` and the initial-segment normal forms `range n`.
-/
theorem eqv_box_canonical
    (p : NormalForm) :
    (p = NormalForm.cofinite [] →
      Provable.Eqv (p.box).toFormula (□(p.toFormula))) ∧
    (∀ n, p = NormalForm.finite (List.range n) →
      Provable.Eqv (p.box).toFormula (□(p.toFormula))) := by
  constructor
  · intro hp
    rw [hp]
    exact eqv_box_top_normalForm
  · intro n hp
    rw [hp]
    exact eqv_box_finite_range_normalForm n

/--
From `a &&& ¬a` we can derive `⊥`.
-/
theorem eqv_conj_neg_self_bottom (a : LetterlessFormula) :
    Provable.Eqv (LetterlessFormula.conj a (LetterlessFormula.neg a)) ⊥ := by
  constructor
  · have ha : Provable (LetterlessFormula.conj a (LetterlessFormula.neg a) ⇒ a) :=
      Provable.conj_elim_left a (LetterlessFormula.neg a)
    have hna : Provable (LetterlessFormula.conj a (LetterlessFormula.neg a) ⇒ LetterlessFormula.neg a) :=
      Provable.conj_elim_right a (LetterlessFormula.neg a)
    exact Provable.imp_mp ha hna
  · exact Provable.ex_falso _

/--
`pulseAt n` implies `iterBoxBottom (n + 1)`.
-/
theorem pulseAt_implies_iterBoxBottom_succ (n : Nat) :
    Provable (LetterlessFormula.pulseAt n ⇒ LetterlessFormula.iterBoxBottom (n + 1)) := by
  exact Provable.imp_trans (eqv_pulseAt_as_conj_iter n).1
    (Provable.conj_elim_left _ _)

/--
`pulseAt n` implies `¬ iterBoxBottom n`.
-/
theorem pulseAt_implies_neg_iterBoxBottom (n : Nat) :
    Provable (LetterlessFormula.pulseAt n ⇒ LetterlessFormula.neg (LetterlessFormula.iterBoxBottom n)) := by
  exact Provable.imp_trans (eqv_pulseAt_as_conj_iter n).1
    (Provable.conj_elim_right _ _)

/--
Distinct pulses are inconsistent when one index is smaller than the other.
-/
theorem eqv_conj_pulse_diff_of_lt {m n : Nat} (h : m < n) :
    Provable.Eqv
      (LetterlessFormula.conj (LetterlessFormula.pulseAt m) (LetterlessFormula.pulseAt n))
      ⊥ := by
  constructor
  · have hm : Provable
        (LetterlessFormula.conj (LetterlessFormula.pulseAt m) (LetterlessFormula.pulseAt n) ⇒
          LetterlessFormula.pulseAt m) :=
      Provable.conj_elim_left _ _
    have hn : Provable
        (LetterlessFormula.conj (LetterlessFormula.pulseAt m) (LetterlessFormula.pulseAt n) ⇒
          LetterlessFormula.pulseAt n) :=
      Provable.conj_elim_right _ _
    have hmn :
        Provable
          (LetterlessFormula.iterBoxBottom (m + 1) ⇒ LetterlessFormula.iterBoxBottom n) :=
      provable_iterBoxBottom_monotone (Nat.succ_le_of_lt h)
    have hpos :
        Provable
          (LetterlessFormula.conj (LetterlessFormula.pulseAt m) (LetterlessFormula.pulseAt n) ⇒
            LetterlessFormula.iterBoxBottom n) :=
      Provable.imp_trans hm (Provable.imp_trans (pulseAt_implies_iterBoxBottom_succ m) hmn)
    have hneg :
        Provable
          (LetterlessFormula.conj (LetterlessFormula.pulseAt m) (LetterlessFormula.pulseAt n) ⇒
            LetterlessFormula.neg (LetterlessFormula.iterBoxBottom n)) :=
      Provable.imp_trans hn (pulseAt_implies_neg_iterBoxBottom n)
    exact Provable.imp_mp hpos hneg
  · exact Provable.ex_falso _

/--
Distinct pulses are inconsistent.
-/
theorem eqv_conj_pulse_diff (m n : Nat) (h : m ≠ n) :
    Provable.Eqv
      (LetterlessFormula.conj (LetterlessFormula.pulseAt m) (LetterlessFormula.pulseAt n))
      ⊥ := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · exact eqv_conj_pulse_diff_of_lt hlt
  · exact Provable.eqv_trans (Provable.eqv_conj_comm _ _)
      (eqv_conj_pulse_diff_of_lt hgt)


/--
If the `finite → finite` implication case is available, then conjunction of a
finite normal form with a cofinite normal form collapses to the finite code for
the set difference.
-/
theorem eqv_conj_finite_cofinite_of_imp_finite_finite
    (hfinite : ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula
        ((NormalForm.finite xs).toFormula ⇒ (NormalForm.finite ys).toFormula)) :
    ∀ xs ys : List Nat,
      Provable.Eqv
        (LetterlessFormula.conj
          (LetterlessFormula.finiteNormalForm xs)
          (LetterlessFormula.cofiniteNormalForm ys))
        (LetterlessFormula.finiteNormalForm (NormalForm.diff xs ys))
  | xs, ys => by
      have h₁ :
          Provable.Eqv
            (LetterlessFormula.conj
              (LetterlessFormula.finiteNormalForm xs)
              (LetterlessFormula.cofiniteNormalForm ys))
            (LetterlessFormula.neg
              (LetterlessFormula.finiteNormalForm xs ⇒
                LetterlessFormula.finiteNormalForm ys)) := by
        unfold LetterlessFormula.conj LetterlessFormula.cofiniteNormalForm
        exact Provable.eqv_neg
          (Provable.eqv_imp
            (Provable.eqv_refl _)
            (Provable.eqv_symm (Provable.eqv_doubleNeg _)))
      have h₂ :
          Provable.Eqv
            (LetterlessFormula.neg
              (LetterlessFormula.finiteNormalForm xs ⇒
                LetterlessFormula.finiteNormalForm ys))
            (LetterlessFormula.neg
              (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula) :=
        Provable.eqv_neg (Provable.eqv_symm (hfinite xs ys))
      have h₃ :
          Provable.Eqv
            (LetterlessFormula.neg
              (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula)
            (LetterlessFormula.finiteNormalForm (NormalForm.diff xs ys)) := by
        simpa [NormalForm.imp, NormalForm.toFormula] using
          eqv_neg_cofiniteNormalForm (NormalForm.diff xs ys)
      exact Provable.eqv_trans h₁ (Provable.eqv_trans h₂ h₃)

/--
`a ⇒ ¬b` is the negation of `a &&& b`.
-/
theorem eqv_imp_neg_as_neg_conj (a b : LetterlessFormula) :
    Provable.Eqv (a ⇒ LetterlessFormula.neg b)
      (LetterlessFormula.neg (LetterlessFormula.conj a b)) := by
  unfold LetterlessFormula.conj
  exact Provable.eqv_doubleNeg (a ⇒ LetterlessFormula.neg b)


/--
`¬⊤` is provably equivalent to `⊥`.
-/
theorem eqv_neg_top_bottom :
    Provable.Eqv (LetterlessFormula.neg LetterlessFormula.top) ⊥ := by
  constructor
  · exact Provable.imp_mp
      (Provable.weaken (a := LetterlessFormula.neg LetterlessFormula.top)
        (b := LetterlessFormula.top) provable_top)
      (Provable.imp_self (LetterlessFormula.neg LetterlessFormula.top))
  · exact Provable.ex_falso _

/--
Conjunction with `⊥` on the left is `⊥`.
-/
theorem eqv_conj_bottom_left (a : LetterlessFormula) :
    Provable.Eqv (LetterlessFormula.conj ⊥ a) ⊥ := by
  have h₁ :
      Provable.Eqv (LetterlessFormula.conj ⊥ a)
        (LetterlessFormula.neg LetterlessFormula.top) := by
    unfold LetterlessFormula.conj LetterlessFormula.neg
    exact Provable.eqv_neg (eqv_of_provable (Provable.ex_falso _))
  exact Provable.eqv_trans h₁ eqv_neg_top_bottom

/--
Conjunction with `⊥` on the right is `⊥`.
-/
theorem eqv_conj_bottom_right (a : LetterlessFormula) :
    Provable.Eqv (LetterlessFormula.conj a ⊥) ⊥ := by
  exact Provable.eqv_trans (Provable.eqv_conj_comm a ⊥) (eqv_conj_bottom_left a)

/--
If conjunction of finite normal forms is available, then the `finite →
cofinite` implication case follows immediately.
-/
theorem eqv_imp_finite_cofinite_of_conj_finite_finite
    (hconj : ∀ xs ys : List Nat,
      Provable.Eqv
        (LetterlessFormula.conj
          (LetterlessFormula.finiteNormalForm xs)
          (LetterlessFormula.finiteNormalForm ys))
        (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys))) :
    ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.finite xs) (NormalForm.cofinite ys)).toFormula
        ((NormalForm.finite xs).toFormula ⇒ (NormalForm.cofinite ys).toFormula)
  | xs, ys => by
      have h₁ :
          Provable.Eqv
            ((NormalForm.finite xs).toFormula ⇒ (NormalForm.cofinite ys).toFormula)
            (LetterlessFormula.neg
              (LetterlessFormula.conj
                (LetterlessFormula.finiteNormalForm xs)
                (LetterlessFormula.finiteNormalForm ys))) := by
        simpa [NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm]
          using (eqv_imp_neg_as_neg_conj
            (LetterlessFormula.finiteNormalForm xs)
            (LetterlessFormula.finiteNormalForm ys))
      have h₂ :
          Provable.Eqv
            (LetterlessFormula.neg
              (LetterlessFormula.conj
                (LetterlessFormula.finiteNormalForm xs)
                (LetterlessFormula.finiteNormalForm ys)))
            (LetterlessFormula.neg
              (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys))) :=
        Provable.eqv_neg (hconj xs ys)
      have h₃ :
          Provable.Eqv
            (LetterlessFormula.neg
              (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys)))
            (NormalForm.imp (NormalForm.finite xs) (NormalForm.cofinite ys)).toFormula := by
        simpa [NormalForm.imp, NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm]
          using (Provable.eqv_refl
            (LetterlessFormula.neg (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys))))
      exact Provable.eqv_trans (Provable.eqv_symm h₃) (Provable.eqv_trans (Provable.eqv_symm h₂) (Provable.eqv_symm h₁))

/--
To prove proof-theoretic correctness of explicit normal-form implication, it is
enough to handle the two genuinely finite cases.
-/
theorem eqv_imp_of_finite_core
    (hfinite : ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula
        ((NormalForm.finite xs).toFormula ⇒ (NormalForm.finite ys).toFormula))
    (hconj : ∀ xs ys : List Nat,
      Provable.Eqv
        (LetterlessFormula.conj
          (LetterlessFormula.finiteNormalForm xs)
          (LetterlessFormula.finiteNormalForm ys))
        (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys))) :
    ∀ p q : NormalForm,
      Provable.Eqv (NormalForm.imp p q).toFormula (p.toFormula ⇒ q.toFormula) :=
  eqv_imp_of_cases
    hfinite
    (eqv_imp_finite_cofinite_of_conj_finite_finite hconj)
    eqv_imp_cofinite_finite
    (eqv_imp_cofinite_cofinite_of_finite hfinite)

/--
To prove conjunction normalization for finite normal forms, it is enough to
know how conjunction distributes over disjunction and how a single pulse meets
an arbitrary finite normal form.
-/
theorem eqv_conj_finiteNormalForm_of_pulse_and_distrib
    (hdistrib : ∀ a b c : LetterlessFormula,
      Provable.Eqv
        (LetterlessFormula.conj (LetterlessFormula.disj a b) c)
        (LetterlessFormula.disj (LetterlessFormula.conj a c) (LetterlessFormula.conj b c)))
    (hpulse : ∀ n : Nat, ∀ ys : List Nat,
      Provable.Eqv
        (LetterlessFormula.conj (LetterlessFormula.pulseAt n) (LetterlessFormula.finiteNormalForm ys))
        (if n ∈ ys then LetterlessFormula.pulseAt n else ⊥)) :
    ∀ xs ys : List Nat,
      Provable.Eqv
        (LetterlessFormula.conj
          (LetterlessFormula.finiteNormalForm xs)
          (LetterlessFormula.finiteNormalForm ys))
        (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys))
  | [], ys => by
      simpa [LetterlessFormula.finiteNormalForm, NormalForm.inter] using
        eqv_conj_bottom_left (LetterlessFormula.finiteNormalForm ys)
  | x :: xs, ys => by
      have h₁ :
          Provable.Eqv
            (LetterlessFormula.conj
              (LetterlessFormula.finiteNormalForm (x :: xs))
              (LetterlessFormula.finiteNormalForm ys))
            (LetterlessFormula.disj
              (LetterlessFormula.conj (LetterlessFormula.pulseAt x) (LetterlessFormula.finiteNormalForm ys))
              (LetterlessFormula.conj (LetterlessFormula.finiteNormalForm xs) (LetterlessFormula.finiteNormalForm ys))) := by
        simpa [LetterlessFormula.finiteNormalForm] using
          hdistrib (LetterlessFormula.pulseAt x) (LetterlessFormula.finiteNormalForm xs)
            (LetterlessFormula.finiteNormalForm ys)
      have h₂ :
          Provable.Eqv
            (LetterlessFormula.disj
              (LetterlessFormula.conj (LetterlessFormula.pulseAt x) (LetterlessFormula.finiteNormalForm ys))
              (LetterlessFormula.conj (LetterlessFormula.finiteNormalForm xs) (LetterlessFormula.finiteNormalForm ys)))
            (LetterlessFormula.disj
              (if x ∈ ys then LetterlessFormula.pulseAt x else ⊥)
              (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys))) := by
        exact Provable.eqv_disj (hpulse x ys) (eqv_conj_finiteNormalForm_of_pulse_and_distrib hdistrib hpulse xs ys)
      by_cases hxy : x ∈ ys
      · have h₃ :
            Provable.Eqv
              (LetterlessFormula.disj (LetterlessFormula.pulseAt x)
                (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys)))
              (LetterlessFormula.finiteNormalForm (NormalForm.inter (x :: xs) ys)) := by
          simpa [LetterlessFormula.finiteNormalForm, NormalForm.inter, hxy] using
            (Provable.eqv_refl
              (LetterlessFormula.disj
                (LetterlessFormula.pulseAt x)
                (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys))))
        exact Provable.eqv_trans h₁ (Provable.eqv_trans h₂ (by simpa [hxy] using h₃))
      · have h₃ :
            Provable.Eqv
              (LetterlessFormula.disj ⊥ (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys)))
              (LetterlessFormula.finiteNormalForm (NormalForm.inter (x :: xs) ys)) := by
          have hleft :
              Provable.Eqv
                (LetterlessFormula.disj ⊥ (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys)))
                (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys)) :=
            Provable.eqv_bottom_disj (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys))
          exact Provable.eqv_trans hleft (by
            simpa [NormalForm.inter, hxy] using
              (Provable.eqv_refl (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys))))
        exact Provable.eqv_trans h₁ (Provable.eqv_trans h₂ (by simpa [hxy] using h₃))

/--
To prove the pulse-vs-finite overlap theorem, it is enough to know
distributivity and the atomic pulse-vs-pulse cases.
-/
theorem eqv_conj_pulse_finiteNormalForm_of_pulse_cases_and_distrib
    (hdistrib : ∀ a b c : LetterlessFormula,
      Provable.Eqv
        (LetterlessFormula.conj (LetterlessFormula.disj a b) c)
        (LetterlessFormula.disj (LetterlessFormula.conj a c) (LetterlessFormula.conj b c)))
    (hpulse_same : ∀ n : Nat,
      Provable.Eqv
        (LetterlessFormula.conj (LetterlessFormula.pulseAt n) (LetterlessFormula.pulseAt n))
        (LetterlessFormula.pulseAt n))
    (hpulse_diff : ∀ m n : Nat, m ≠ n →
      Provable.Eqv
        (LetterlessFormula.conj (LetterlessFormula.pulseAt m) (LetterlessFormula.pulseAt n))
        ⊥) :
    ∀ n : Nat, ∀ ys : List Nat,
      Provable.Eqv
        (LetterlessFormula.conj (LetterlessFormula.pulseAt n) (LetterlessFormula.finiteNormalForm ys))
        (if n ∈ ys then LetterlessFormula.pulseAt n else ⊥)
  | n, [] => by
      simpa [LetterlessFormula.finiteNormalForm] using
        eqv_conj_bottom_right (LetterlessFormula.pulseAt n)
  | n, y :: ys => by
      have h₁ :
          Provable.Eqv
            (LetterlessFormula.conj
              (LetterlessFormula.pulseAt n)
              (LetterlessFormula.finiteNormalForm (y :: ys)))
            (LetterlessFormula.disj
              (LetterlessFormula.conj (LetterlessFormula.pulseAt y) (LetterlessFormula.pulseAt n))
              (LetterlessFormula.conj (LetterlessFormula.finiteNormalForm ys) (LetterlessFormula.pulseAt n))) := by
        have hcomm :
            Provable.Eqv
              (LetterlessFormula.conj
                (LetterlessFormula.pulseAt n)
                (LetterlessFormula.finiteNormalForm (y :: ys)))
              (LetterlessFormula.conj
                (LetterlessFormula.finiteNormalForm (y :: ys))
                (LetterlessFormula.pulseAt n)) :=
          Provable.eqv_conj_comm _ _
        have hdist :
            Provable.Eqv
              (LetterlessFormula.conj
                (LetterlessFormula.finiteNormalForm (y :: ys))
                (LetterlessFormula.pulseAt n))
              (LetterlessFormula.disj
                (LetterlessFormula.conj (LetterlessFormula.pulseAt y) (LetterlessFormula.pulseAt n))
                (LetterlessFormula.conj (LetterlessFormula.finiteNormalForm ys) (LetterlessFormula.pulseAt n))) := by
          simpa [LetterlessFormula.finiteNormalForm] using
            hdistrib (LetterlessFormula.pulseAt y) (LetterlessFormula.finiteNormalForm ys)
              (LetterlessFormula.pulseAt n)
        exact Provable.eqv_trans hcomm hdist
      have h₂ :
          Provable.Eqv
            (LetterlessFormula.disj
              (LetterlessFormula.conj (LetterlessFormula.pulseAt y) (LetterlessFormula.pulseAt n))
              (LetterlessFormula.conj (LetterlessFormula.finiteNormalForm ys) (LetterlessFormula.pulseAt n)))
            (LetterlessFormula.disj
              (if y = n then LetterlessFormula.pulseAt n else ⊥)
              (if n ∈ ys then LetterlessFormula.pulseAt n else ⊥)) := by
        have hp1 :
            Provable.Eqv
              (LetterlessFormula.conj (LetterlessFormula.pulseAt y) (LetterlessFormula.pulseAt n))
              (if y = n then LetterlessFormula.pulseAt n else ⊥) := by
          by_cases hy : y = n
          · simpa [hy] using hpulse_same n
          · simpa [hy] using hpulse_diff y n hy
        have hp2 :
            Provable.Eqv
              (LetterlessFormula.conj (LetterlessFormula.finiteNormalForm ys) (LetterlessFormula.pulseAt n))
              (if n ∈ ys then LetterlessFormula.pulseAt n else ⊥) := by
          exact Provable.eqv_trans
            (Provable.eqv_conj_comm _ _)
            (eqv_conj_pulse_finiteNormalForm_of_pulse_cases_and_distrib
              hdistrib hpulse_same hpulse_diff n ys)
        exact Provable.eqv_disj hp1 hp2
      by_cases hy : y = n
      · by_cases hmem : n ∈ ys
        · have h₃ :
              Provable.Eqv
                (LetterlessFormula.disj (LetterlessFormula.pulseAt n) (LetterlessFormula.pulseAt n))
                (LetterlessFormula.pulseAt n) :=
            Provable.eqv_disj_idem (LetterlessFormula.pulseAt n)
          exact Provable.eqv_trans h₁ <|
            Provable.eqv_trans h₂ <|
              by simpa [hmem, hy, eq_comm]
                using h₃
        · have h₃ :
              Provable.Eqv
                (LetterlessFormula.disj (LetterlessFormula.pulseAt n) ⊥)
                (LetterlessFormula.pulseAt n) :=
            Provable.eqv_disj_bottom (LetterlessFormula.pulseAt n)
          exact Provable.eqv_trans h₁ <|
            Provable.eqv_trans h₂ <|
              by simpa [hmem, hy, eq_comm]
                using h₃
      · by_cases hmem : n ∈ ys
        · have h₃ :
              Provable.Eqv
                (LetterlessFormula.disj ⊥ (LetterlessFormula.pulseAt n))
                (LetterlessFormula.pulseAt n) :=
            Provable.eqv_bottom_disj (LetterlessFormula.pulseAt n)
          exact Provable.eqv_trans h₁ <|
            Provable.eqv_trans h₂ <|
              by simpa [hy, hmem, eq_comm]
                using h₃
        · have h₃ :
              Provable.Eqv (LetterlessFormula.disj ⊥ ⊥) ⊥ :=
            Provable.eqv_bottom_disj ⊥
          have hny : ¬ n = y := by
            intro h
            exact hy h.symm
          exact Provable.eqv_trans h₁ <|
            Provable.eqv_trans h₂ <|
              by simpa [hy, hny, hmem, eq_comm]
                using h₃

/--
Pulse versus finite normal form.
-/
theorem eqv_conj_pulse_finiteNormalForm
    (n : Nat) (ys : List Nat) :
    Provable.Eqv
      (LetterlessFormula.conj (LetterlessFormula.pulseAt n) (LetterlessFormula.finiteNormalForm ys))
      (if n ∈ ys then LetterlessFormula.pulseAt n else ⊥) :=
  eqv_conj_pulse_finiteNormalForm_of_pulse_cases_and_distrib
    Provable.eqv_conj_disj_left
    eqv_conj_pulse_same
    eqv_conj_pulse_diff
    n ys

/--
Conjunction of two finite normal forms collapses to the finite normal form for
their list intersection.
-/
theorem eqv_conj_finiteNormalForm
    (xs ys : List Nat) :
    Provable.Eqv
      (LetterlessFormula.conj
        (LetterlessFormula.finiteNormalForm xs)
        (LetterlessFormula.finiteNormalForm ys))
      (LetterlessFormula.finiteNormalForm (NormalForm.inter xs ys)) :=
  eqv_conj_finiteNormalForm_of_pulse_and_distrib
    Provable.eqv_conj_disj_left
    eqv_conj_pulse_finiteNormalForm
    xs ys

/--
If `n ∈ ys`, then the pulse at `n` implies the finite normal form on `ys`.
-/
theorem pulseAt_implies_finiteNormalForm_of_mem
    (n : Nat) (ys : List Nat) (hmem : n ∈ ys) :
    Provable (LetterlessFormula.pulseAt n ⇒ LetterlessFormula.finiteNormalForm ys) := by
  have hconj :
      Provable.Eqv
        (LetterlessFormula.conj (LetterlessFormula.pulseAt n) (LetterlessFormula.finiteNormalForm ys))
        (LetterlessFormula.pulseAt n) := by
    simpa [hmem] using eqv_conj_pulse_finiteNormalForm n ys
  exact Provable.imp_trans hconj.2
    (Provable.conj_elim_right (LetterlessFormula.pulseAt n) (LetterlessFormula.finiteNormalForm ys))

/--
Finite normal forms are monotone with respect to membership inclusion.
-/
theorem provable_finiteNormalForm_mono
    {xs ys : List Nat}
    (hsub : ∀ t : Nat, t ∈ xs → t ∈ ys) :
    Provable (LetterlessFormula.finiteNormalForm xs ⇒ LetterlessFormula.finiteNormalForm ys) := by
  induction xs with
  | nil =>
      simpa [LetterlessFormula.finiteNormalForm] using Provable.ex_falso (LetterlessFormula.finiteNormalForm ys)
  | cons x xs ih =>
      have hx :
          Provable (LetterlessFormula.pulseAt x ⇒ LetterlessFormula.finiteNormalForm ys) :=
        pulseAt_implies_finiteNormalForm_of_mem x ys (hsub x (by simp))
      have hxs :
          Provable (LetterlessFormula.finiteNormalForm xs ⇒ LetterlessFormula.finiteNormalForm ys) :=
        ih (fun t ht => hsub t (List.mem_cons_of_mem _ ht))
      simpa [LetterlessFormula.finiteNormalForm] using
        Provable.disj_elim hx hxs

/--
Cofinite normal forms are anti-monotone with respect to hole inclusion.
-/
theorem provable_cofiniteNormalForm_antimono
    {xs ys : List Nat}
    (hsub : ∀ t : Nat, t ∈ xs → t ∈ ys) :
    Provable (LetterlessFormula.cofiniteNormalForm ys ⇒ LetterlessFormula.cofiniteNormalForm xs) := by
  have hfin :
      Provable
        (LetterlessFormula.finiteNormalForm xs ⇒
          LetterlessFormula.finiteNormalForm ys) :=
    provable_finiteNormalForm_mono hsub
  have hcontra :
      Provable
        (LetterlessFormula.neg (LetterlessFormula.finiteNormalForm ys) ⇒
          LetterlessFormula.neg (LetterlessFormula.finiteNormalForm xs)) :=
    Provable.modusPonens
      (Provable.eqv_contrapositive
        (LetterlessFormula.finiteNormalForm ys)
        (LetterlessFormula.finiteNormalForm xs)).2
      hfin
  simpa [LetterlessFormula.cofiniteNormalForm] using
    hcontra

/--
Finite normal forms with the same membership relation are provably equivalent.
-/
theorem eqv_finiteNormalForm_of_same_membership
    {xs ys : List Nat}
    (hxy : ∀ t : Nat, t ∈ xs → t ∈ ys)
    (hyx : ∀ t : Nat, t ∈ ys → t ∈ xs) :
    Provable.Eqv
      (LetterlessFormula.finiteNormalForm xs)
      (LetterlessFormula.finiteNormalForm ys) :=
  ⟨provable_finiteNormalForm_mono hxy, provable_finiteNormalForm_mono hyx⟩

/--
If a finite normal form has the same denotation as `□^n⊥`, then it is
provably equivalent to `□^n⊥`.
-/
theorem eqv_finiteNormalForm_of_eval_eq_iterBoxBottom
    (xs : List Nat) (n : Nat)
    (h :
      LetterlessFormula.eval (LetterlessFormula.finiteNormalForm xs) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv
      (LetterlessFormula.finiteNormalForm xs)
      (LetterlessFormula.iterBoxBottom n) := by
  have hxy : ∀ t : Nat, t ∈ xs → t ∈ List.range n := by
    intro t ht
    have htrue :
        LetterlessFormula.eval (LetterlessFormula.finiteNormalForm xs) t = true :=
      (LetterlessFormula.eval_finiteNormalForm_true_iff xs t).2 ht
    have htrue' :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) t = true := by
      simpa [htrue] using congrArg (fun f => f t) h
    simp [List.mem_range, (LetterlessFormula.eval_iterBoxBottom_true_iff n t).1 htrue']
  have hyx : ∀ t : Nat, t ∈ List.range n → t ∈ xs := by
    intro t ht
    have htrue :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) t = true := by
      exact (LetterlessFormula.eval_iterBoxBottom_true_iff n t).2 (by simpa [List.mem_range] using ht)
    have htrue' :
        LetterlessFormula.eval (LetterlessFormula.finiteNormalForm xs) t = true := by
      simpa [htrue] using (congrArg (fun f => f t) h).symm
    exact (LetterlessFormula.eval_finiteNormalForm_true_iff xs t).1 htrue'
  exact Provable.eqv_trans
    (eqv_finiteNormalForm_of_same_membership hxy hyx)
    (eqv_finite_range_iterBoxBottom n)

/--
A cofinite normal form can never have the same denotation as an initial
segment `□^n⊥`.
-/
theorem eval_cofiniteNormalForm_ne_iterBoxBottom
    (xs : List Nat) (n : Nat) :
    LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) ≠
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
  intro h
  let t := succAbove (n :: xs)
  have htNotMem : t ∉ xs := by
    intro hmem
    have : t ∈ n :: xs := List.mem_cons_of_mem _ hmem
    exact not_mem_succAbove (n :: xs) this
  have htGe : n ≤ t := by
    exact Nat.le_of_lt (lt_succAbove_of_mem (by simp))
  have hcof :
      LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) t = true := by
    rw [LetterlessFormula.eval_cofiniteNormalForm]
    simp [htNotMem]
  have hiter :
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) t = false := by
    cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) t with
    | false => exact rfl
    | true =>
        exact False.elim
          (Nat.not_lt_of_ge htGe
            ((LetterlessFormula.eval_iterBoxBottom_true_iff n t).1 hval))
  have hcontra := congrArg (fun f => f t) h
  simp [hcof, hiter] at hcontra

/--
If two cofinite normal forms have the same set of holes, they are provably
equivalent.
-/
theorem eqv_cofiniteNormalForm_of_same_nonmembership
    {xs ys : List Nat}
    (hxy : ∀ t : Nat, t ∉ xs → t ∉ ys)
    (hyx : ∀ t : Nat, t ∉ ys → t ∉ xs) :
    Provable.Eqv
      (LetterlessFormula.cofiniteNormalForm xs)
      (LetterlessFormula.cofiniteNormalForm ys) := by
  classical
  have hfin :
      Provable.Eqv
        (LetterlessFormula.finiteNormalForm xs)
        (LetterlessFormula.finiteNormalForm ys) := by
    apply eqv_finiteNormalForm_of_same_membership
    · intro t ht
      by_cases hmem : t ∈ ys
      · exact hmem
      · exact False.elim ((hyx t hmem) ht)
    · intro t ht
      by_cases hmem : t ∈ xs
      · exact hmem
      · exact False.elim ((hxy t hmem) ht)
  simpa [LetterlessFormula.cofiniteNormalForm] using Provable.eqv_neg hfin

/--
A finite normal form can never have the same denotation as a cofinite normal
form.
-/
theorem eval_finiteNormalForm_ne_cofiniteNormalForm
    (xs ys : List Nat) :
    LetterlessFormula.eval (LetterlessFormula.finiteNormalForm xs) ≠
      LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm ys) := by
  intro h
  let t := succAbove (xs ++ ys)
  have hnotxs : t ∉ xs := by
    intro hmem
    exact not_mem_succAbove (xs ++ ys) (List.mem_append.mpr (Or.inl hmem))
  have hnotys : t ∉ ys := by
    intro hmem
    exact not_mem_succAbove (xs ++ ys) (List.mem_append.mpr (Or.inr hmem))
  have hfin :
      LetterlessFormula.eval (LetterlessFormula.finiteNormalForm xs) t = false := by
    rw [LetterlessFormula.eval_finiteNormalForm]
    simp [hnotxs]
  have hcof :
      LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm ys) t = true := by
    rw [LetterlessFormula.eval_cofiniteNormalForm]
    simp [hnotys]
  have hcontra := congrArg (fun f => f t) h
  simp [hfin, hcof] at hcontra

/--
Among normal forms, those with the same denotation as a given finite normal
form are provably equivalent to it.
-/
theorem eqv_normalForm_of_eval_eq_finiteNormalForm
    (nf : NormalForm) (ys : List Nat)
    (h :
      LetterlessFormula.eval nf.toFormula =
        LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys)) :
    Provable.Eqv nf.toFormula (LetterlessFormula.finiteNormalForm ys) := by
  cases nf with
  | finite xs =>
      have hxy : ∀ t : Nat, t ∈ xs → t ∈ ys := by
        intro t ht
        have htrue :
            LetterlessFormula.eval (LetterlessFormula.finiteNormalForm xs) t = true :=
          (LetterlessFormula.eval_finiteNormalForm_true_iff xs t).2 ht
        have htrue' :
            LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) t = true := by
          have hEqt := congrArg (fun f => f t) h
          simpa [NormalForm.toFormula, htrue] using hEqt
        exact (LetterlessFormula.eval_finiteNormalForm_true_iff ys t).1 htrue'
      have hyx : ∀ t : Nat, t ∈ ys → t ∈ xs := by
        intro t ht
        have htrue :
            LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) t = true :=
          (LetterlessFormula.eval_finiteNormalForm_true_iff ys t).2 ht
        have htrue' :
            LetterlessFormula.eval (LetterlessFormula.finiteNormalForm xs) t = true := by
          have hEqt := (congrArg (fun f => f t) h).symm
          simpa [NormalForm.toFormula, htrue] using hEqt
        exact (LetterlessFormula.eval_finiteNormalForm_true_iff xs t).1 htrue'
      simpa [NormalForm.toFormula] using eqv_finiteNormalForm_of_same_membership hxy hyx
  | cofinite xs =>
      exact False.elim (eval_finiteNormalForm_ne_cofiniteNormalForm ys xs h.symm)

/--
Among normal forms, those with the same denotation as a given cofinite normal
form are provably equivalent to it.
-/
theorem eqv_normalForm_of_eval_eq_cofiniteNormalForm
    (nf : NormalForm) (xs : List Nat)
    (h :
      LetterlessFormula.eval nf.toFormula =
        LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs)) :
    Provable.Eqv nf.toFormula (LetterlessFormula.cofiniteNormalForm xs) := by
  cases nf with
  | finite ys =>
      exact False.elim (eval_finiteNormalForm_ne_cofiniteNormalForm ys xs h)
  | cofinite ys =>
      have hxy : ∀ t : Nat, t ∉ ys → t ∉ xs := by
        intro t ht
        have htrue :
            LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm ys) t = true :=
          (LetterlessFormula.eval_cofiniteNormalForm_true_iff ys t).2 ht
        have htrue' :
            LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) t = true := by
          have hEqt := congrArg (fun f => f t) h
          simpa [NormalForm.toFormula, htrue] using hEqt
        exact (LetterlessFormula.eval_cofiniteNormalForm_true_iff xs t).1 htrue'
      have hyx : ∀ t : Nat, t ∉ xs → t ∉ ys := by
        intro t ht
        have htrue :
            LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) t = true :=
          (LetterlessFormula.eval_cofiniteNormalForm_true_iff xs t).2 ht
        have htrue' :
            LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm ys) t = true := by
          have hEqt := (congrArg (fun f => f t) h).symm
          simpa [NormalForm.toFormula, htrue] using hEqt
        exact (LetterlessFormula.eval_cofiniteNormalForm_true_iff ys t).1 htrue'
      simpa [NormalForm.toFormula] using eqv_cofiniteNormalForm_of_same_nonmembership hxy hyx

/--
If a recursive normal form denotes an initial segment, it is necessarily a
finite normal form.
-/
theorem exists_finite_shape_of_eval_eq_iterBoxBottom
    (nf : NormalForm) (n : Nat)
    (h :
      LetterlessFormula.eval nf.toFormula =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    ∃ ys : List Nat, nf = NormalForm.finite ys := by
  cases nf with
  | finite ys =>
      exact ⟨ys, rfl⟩
  | cofinite xs =>
      exact False.elim (eval_cofiniteNormalForm_ne_iterBoxBottom xs n h)

/--
Among normal forms, only finite normal forms can denote an initial segment, and
in that case they are provably equivalent to the corresponding `□^n⊥`.
-/
theorem eqv_normalForm_of_eval_eq_iterBoxBottom
    (nf : NormalForm) (n : Nat)
    (h :
      LetterlessFormula.eval nf.toFormula =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv nf.toFormula (LetterlessFormula.iterBoxBottom n) := by
  cases nf with
  | finite xs =>
      simpa [NormalForm.toFormula] using
        eqv_finiteNormalForm_of_eval_eq_iterBoxBottom xs n h
  | cofinite xs =>
      exact False.elim (eval_cofiniteNormalForm_ne_iterBoxBottom xs n h)

/--
If an explicit normal-form implication denotes an initial segment, then it must
come from the `cofinite → finite` case.
-/
theorem imp_case_of_eval_eq_iterBoxBottom
    (p q : NormalForm) (n : Nat)
    (h :
      LetterlessFormula.eval (NormalForm.imp p q).toFormula =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    ∃ xs ys, p = NormalForm.cofinite xs ∧ q = NormalForm.finite ys := by
  cases p <;> cases q
  · exact False.elim (eval_cofiniteNormalForm_ne_iterBoxBottom _ _ h)
  · exact False.elim (eval_cofiniteNormalForm_ne_iterBoxBottom _ _ h)
  · exact ⟨_, _, rfl, rfl⟩
  · exact False.elim (eval_cofiniteNormalForm_ne_iterBoxBottom _ _ h)

/--
In the implication initial-segment case, the normalizer must be in the explicit
`cofinite → finite` shape.
-/
theorem normalize_imp_case_of_eval_eq_iterBoxBottom
    (a b : LetterlessFormula) (n : Nat)
    (h :
      LetterlessFormula.eval (a ⇒ b) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    ∃ xs ys,
      normalize a = NormalForm.cofinite xs ∧
      normalize b = NormalForm.finite ys := by
  have hnorm :
      LetterlessFormula.eval (NormalForm.imp (normalize a) (normalize b)).toFormula =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
    calc
      LetterlessFormula.eval (NormalForm.imp (normalize a) (normalize b)).toFormula =
        (LetterlessFormula.eval (normalize a).toFormula =⇒
          LetterlessFormula.eval (normalize b).toFormula) := by
          simpa using NormalForm.eval_imp (normalize a) (normalize b)
      _ = (LetterlessFormula.eval a =⇒ LetterlessFormula.eval b) := by
          simp [eval_normalize]
      _ = LetterlessFormula.eval (a ⇒ b) := by
          symm
          exact LetterlessFormula.eval_imp a b
      _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
  rcases imp_case_of_eval_eq_iterBoxBottom (normalize a) (normalize b) n hnorm with
    ⟨xs, ys, hpa, hqb⟩
  exact ⟨xs, ys, hpa, hqb⟩

/--
In the implication initial-segment case, the explicit `cofinite → finite`
normal form has exactly the corresponding initial-segment denotation.
-/
theorem normalize_imp_cofinite_finite_eval_eq_iterBoxBottom
    (a b : LetterlessFormula) (n : Nat)
    (xs ys : List Nat)
    (hpa : normalize a = NormalForm.cofinite xs)
    (hqb : normalize b = NormalForm.finite ys)
    (h :
      LetterlessFormula.eval (a ⇒ b) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    LetterlessFormula.eval (LetterlessFormula.finiteNormalForm (xs ++ ys)) =
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
  calc
    LetterlessFormula.eval (LetterlessFormula.finiteNormalForm (xs ++ ys)) =
      LetterlessFormula.eval (NormalForm.imp (normalize a) (normalize b)).toFormula := by
        simp [hpa, hqb, NormalForm.imp, NormalForm.toFormula]
    _ = LetterlessFormula.eval (a ⇒ b) := by
        calc
          LetterlessFormula.eval (NormalForm.imp (normalize a) (normalize b)).toFormula =
            (LetterlessFormula.eval (normalize a).toFormula =⇒
              LetterlessFormula.eval (normalize b).toFormula) := by
              simpa using NormalForm.eval_imp (normalize a) (normalize b)
          _ = (LetterlessFormula.eval a =⇒ LetterlessFormula.eval b) := by
              simp [eval_normalize]
          _ = LetterlessFormula.eval (a ⇒ b) := by
              symm
              exact LetterlessFormula.eval_imp a b
    _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h


/--
If a formula is provably equivalent to its chosen normal form, then any
initial-segment denotation immediately yields provable equivalence to the
corresponding iterated-bottom formula.
-/
theorem eqv_of_eval_eq_iterBoxBottom_and_normalForm
    (a : LetterlessFormula) (n : Nat)
    (hnf : Provable.Eqv a (normalFormOf a).toFormula)
    (h :
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv a (LetterlessFormula.iterBoxBottom n) := by
  have hnfEval :
      LetterlessFormula.eval (normalFormOf a).toFormula =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
    calc
      LetterlessFormula.eval (normalFormOf a).toFormula = LetterlessFormula.eval a :=
        eval_normalFormOf a
      _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
  exact Provable.eqv_trans hnf
    (eqv_normalForm_of_eval_eq_iterBoxBottom (normalFormOf a) n hnfEval)

/--
Likewise, if a formula is provably equivalent to its recursive normal form in
an initial-segment case, then it is provably equivalent to the corresponding
iterated-bottom formula.
-/
theorem eqv_of_eval_eq_iterBoxBottom_and_normalize
    (a : LetterlessFormula) (n : Nat)
    (hnorm : Provable.Eqv a (normalize a).toFormula)
    (h :
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv a (LetterlessFormula.iterBoxBottom n) := by
  have hnormEval :
      LetterlessFormula.eval (normalize a).toFormula =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
    calc
      LetterlessFormula.eval (normalize a).toFormula = LetterlessFormula.eval a :=
        eval_normalize a
      _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
  exact Provable.eqv_trans hnorm
    (eqv_normalForm_of_eval_eq_iterBoxBottom (normalize a) n hnormEval)

/--
If a formula denotes an initial segment, then its recursive normal form is
provably equivalent to the corresponding iterated-bottom formula.
-/
theorem eqv_normalize_to_iterBoxBottom_of_eval_eq
    (a : LetterlessFormula) (n : Nat)
    (h :
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv (normalize a).toFormula (LetterlessFormula.iterBoxBottom n) := by
  have hnormEval :
      LetterlessFormula.eval (normalize a).toFormula =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
    calc
      LetterlessFormula.eval (normalize a).toFormula = LetterlessFormula.eval a :=
        eval_normalize a
      _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
  exact eqv_normalForm_of_eval_eq_iterBoxBottom (normalize a) n hnormEval

/--
For formulas with initial-segment semantics, equivalence to the corresponding
iterated-bottom formula is equivalent to equivalence to the recursive normal
form.
-/
theorem eqv_iterBoxBottom_iff_eqv_normalize_of_eval_eq
    (a : LetterlessFormula) (n : Nat)
    (h :
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv a (LetterlessFormula.iterBoxBottom n) ↔
      Provable.Eqv a (normalize a).toFormula := by
  constructor
  · intro hiter
    exact Provable.eqv_trans hiter
      (Provable.eqv_symm (eqv_normalize_to_iterBoxBottom_of_eval_eq a n h))
  · intro hnorm
    exact Provable.eqv_trans hnorm
      (eqv_normalize_to_iterBoxBottom_of_eval_eq a n h)

/--
`⊥` has the same denotation as `□^n⊥` only when `n = 0`.
-/
theorem eval_bottom_eq_iterBoxBottom_iff_zero {n : Nat}
    (h :
      LetterlessFormula.eval ⊥ =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    n = 0 := by
  have hzero :
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) 0 = false := by
    simpa [LetterlessFormula.eval_bottom, const0, const] using congrArg (fun f => f 0) h
  cases n with
  | zero =>
      rfl
  | succ n =>
      have htrue :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (Nat.succ n)) 0 = true :=
        (LetterlessFormula.eval_iterBoxBottom_true_iff (Nat.succ n) 0).2 (Nat.succ_pos _)
      simp [htrue] at hzero

/--
Initial-segment normalization reduces to the implication and box cases; the
bottom case is automatic.
-/
theorem eqv_initialSegment_recursive_of_cases
    (himp : ∀ a b : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (a ⇒ b) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (a ⇒ b) (normalize (a ⇒ b)).toFormula)
    (hbox : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (normalize (□a)).toFormula) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv a (normalize a).toFormula
  | ⊥, n, h => by
      have hn : n = 0 := eval_bottom_eq_iterBoxBottom_iff_zero h
      subst hn
      exact Provable.eqv_refl _
  | a ⇒ b, n, h => himp a b n h
  | □a, n, h => hbox a n h

/--
For the implication case, equivalence to the recursive normal form is
equivalent to equivalence to the corresponding iterated-bottom formula.
-/
theorem eqv_initialSegment_imp_iff_iterBoxBottom
    (a b : LetterlessFormula) (n : Nat)
    (h :
      LetterlessFormula.eval (a ⇒ b) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv (a ⇒ b) (normalize (a ⇒ b)).toFormula ↔
      Provable.Eqv (a ⇒ b) (LetterlessFormula.iterBoxBottom n) :=
  (eqv_iterBoxBottom_iff_eqv_normalize_of_eval_eq (a ⇒ b) n h).symm

/--
For the box case, equivalence to the recursive normal form is equivalent to
equivalence to the corresponding iterated-bottom formula.
-/
theorem eqv_initialSegment_box_iff_iterBoxBottom
    (a : LetterlessFormula) (n : Nat)
    (h :
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv (□a) (normalize (□a)).toFormula ↔
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n) :=
  (eqv_iterBoxBottom_iff_eqv_normalize_of_eval_eq (□a) n h).symm

/--
Restated in the sharpest form currently available: full recursive
normalization follows if the implication and box formulas with initial-segment
semantics are provably equivalent to the corresponding iterated-bottom
formulas.
-/
theorem eqv_initialSegment_recursive_of_iter_cases
    (himp : ∀ a b : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (a ⇒ b) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (a ⇒ b) (LetterlessFormula.iterBoxBottom n))
    (hbox : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n)) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv a (normalize a).toFormula :=
  eqv_initialSegment_recursive_of_cases
    (fun a b n h => (eqv_initialSegment_imp_iff_iterBoxBottom a b n h).2 (himp a b n h))
    (fun a n h => (eqv_initialSegment_box_iff_iterBoxBottom a n h).2 (hbox a n h))

/--
The `finite → cofinite` implication case.
-/
theorem eqv_imp_finite_cofinite :
    ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.finite xs) (NormalForm.cofinite ys)).toFormula
        ((NormalForm.finite xs).toFormula ⇒ (NormalForm.cofinite ys).toFormula) :=
  eqv_imp_finite_cofinite_of_conj_finite_finite eqv_conj_finiteNormalForm



/--
Conjunction with `⊤` on the left is neutral.
-/
theorem eqv_conj_top_left (a : LetterlessFormula) :
    Provable.Eqv (LetterlessFormula.conj LetterlessFormula.top a) a := by
  constructor
  · exact Provable.conj_elim_right _ _
  · exact Provable.conj_intro _ _ _
      (Provable.weaken (a := a) provable_top)
      (Provable.imp_self a)

/--
Conjunction with `⊤` on the right is neutral.
-/
theorem eqv_conj_top_right (a : LetterlessFormula) :
    Provable.Eqv (LetterlessFormula.conj a LetterlessFormula.top) a := by
  exact Provable.eqv_trans (Provable.eqv_conj_comm _ _) (eqv_conj_top_left a)

/--
Conjoining a pulse with a cofinite normal form.
-/
theorem eqv_conj_pulse_cofiniteNormalForm
    (n : Nat) (ys : List Nat) :
    Provable.Eqv
      (LetterlessFormula.conj
        (LetterlessFormula.pulseAt n)
        (LetterlessFormula.cofiniteNormalForm ys))
      (if n ∈ ys then ⊥ else LetterlessFormula.pulseAt n) := by
  by_cases hmem : n ∈ ys
  · have hpf :
        Provable.Eqv
          (LetterlessFormula.conj
            (LetterlessFormula.pulseAt n)
            (LetterlessFormula.finiteNormalForm ys))
          (LetterlessFormula.pulseAt n) := by
      simpa [hmem] using eqv_conj_pulse_finiteNormalForm n ys
    have hp_to_fin :
        Provable (LetterlessFormula.pulseAt n ⇒ LetterlessFormula.finiteNormalForm ys) :=
      Provable.imp_trans hpf.2 (Provable.conj_elim_right _ _)
    constructor
    · simpa [hmem] using (by
        have hp : Provable
            (LetterlessFormula.conj
              (LetterlessFormula.pulseAt n)
              (LetterlessFormula.cofiniteNormalForm ys) ⇒ LetterlessFormula.pulseAt n) :=
          Provable.conj_elim_left _ _
        have hneg : Provable
            (LetterlessFormula.conj
              (LetterlessFormula.pulseAt n)
              (LetterlessFormula.cofiniteNormalForm ys) ⇒
                LetterlessFormula.neg (LetterlessFormula.finiteNormalForm ys)) := by
          simpa [LetterlessFormula.cofiniteNormalForm] using
            (Provable.conj_elim_right
              (LetterlessFormula.pulseAt n)
              (LetterlessFormula.cofiniteNormalForm ys))
        have hfin :
            Provable
              (LetterlessFormula.conj
                (LetterlessFormula.pulseAt n)
                (LetterlessFormula.cofiniteNormalForm ys) ⇒
                  LetterlessFormula.finiteNormalForm ys) :=
          Provable.imp_trans hp hp_to_fin
        exact Provable.imp_mp hfin hneg)
    · simpa [hmem] using (Provable.ex_falso
        (LetterlessFormula.conj
          (LetterlessFormula.pulseAt n)
          (LetterlessFormula.cofiniteNormalForm ys)))
  · constructor
    · simpa [hmem] using (Provable.conj_elim_left
        (LetterlessFormula.pulseAt n)
        (LetterlessFormula.cofiniteNormalForm ys))
    · simpa [hmem] using (by
        have hpfbot :
            Provable
              (LetterlessFormula.conj
                (LetterlessFormula.pulseAt n)
                (LetterlessFormula.finiteNormalForm ys) ⇒ ⊥) := by
          simpa [hmem] using (eqv_conj_pulse_finiteNormalForm n ys).1
        have hcur :
            Provable
              (LetterlessFormula.pulseAt n ⇒
                (LetterlessFormula.finiteNormalForm ys ⇒
                  LetterlessFormula.conj
                    (LetterlessFormula.pulseAt n)
                    (LetterlessFormula.finiteNormalForm ys))) :=
          Provable.conj_intro_curried _ _
        have hpost :
            Provable
              ((LetterlessFormula.finiteNormalForm ys ⇒
                  LetterlessFormula.conj
                    (LetterlessFormula.pulseAt n)
                    (LetterlessFormula.finiteNormalForm ys)) ⇒
                (LetterlessFormula.finiteNormalForm ys ⇒ ⊥)) :=
          Provable.modusPonens
            (Provable.imp_compose
              (LetterlessFormula.finiteNormalForm ys)
              (LetterlessFormula.conj
                (LetterlessFormula.pulseAt n)
                (LetterlessFormula.finiteNormalForm ys))
              ⊥)
            hpfbot
        have hpcof :
            Provable
              (LetterlessFormula.pulseAt n ⇒
                LetterlessFormula.cofiniteNormalForm ys) := by
          have hneg :
              Provable
                (LetterlessFormula.pulseAt n ⇒
                  (LetterlessFormula.finiteNormalForm ys ⇒ ⊥)) :=
            Provable.imp_mp hcur (Provable.weaken (a := LetterlessFormula.pulseAt n) hpost)
          simpa [LetterlessFormula.cofiniteNormalForm] using hneg
        exact Provable.conj_intro _ _ _
          (Provable.imp_self (LetterlessFormula.pulseAt n))
          hpcof)

/--
Implication from a pulse into a finite normal form.
-/
theorem eqv_imp_pulse_finiteNormalForm
    (n : Nat) (ys : List Nat) :
    Provable.Eqv
      (LetterlessFormula.imp (LetterlessFormula.pulseAt n) (LetterlessFormula.finiteNormalForm ys))
      (if n ∈ ys then LetterlessFormula.top else LetterlessFormula.cofiniteNormalForm [n]) := by
  have h₁ :
      Provable.Eqv
        (LetterlessFormula.imp (LetterlessFormula.pulseAt n) (LetterlessFormula.finiteNormalForm ys))
        (LetterlessFormula.neg
          (LetterlessFormula.conj
            (LetterlessFormula.pulseAt n)
            (LetterlessFormula.cofiniteNormalForm ys))) := by
    have hbase :
        Provable.Eqv
          (LetterlessFormula.imp
            (LetterlessFormula.pulseAt n)
            (LetterlessFormula.neg (LetterlessFormula.cofiniteNormalForm ys)))
          (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.pulseAt n)
              (LetterlessFormula.cofiniteNormalForm ys))) :=
      eqv_imp_neg_as_neg_conj
        (LetterlessFormula.pulseAt n)
        (LetterlessFormula.cofiniteNormalForm ys)
    have hnegcof :
        Provable.Eqv
          (LetterlessFormula.neg (LetterlessFormula.cofiniteNormalForm ys))
          (LetterlessFormula.finiteNormalForm ys) :=
      eqv_neg_cofiniteNormalForm ys
    exact Provable.eqv_trans
      (Provable.eqv_imp (Provable.eqv_refl _) (Provable.eqv_symm hnegcof))
      hbase
  by_cases hmem : n ∈ ys
  · have hcof :
        Provable.Eqv
          (LetterlessFormula.conj
            (LetterlessFormula.pulseAt n)
            (LetterlessFormula.cofiniteNormalForm ys))
          ⊥ := by
      simpa [hmem] using eqv_conj_pulse_cofiniteNormalForm n ys
    have hneg :
        Provable.Eqv
          (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.pulseAt n)
              (LetterlessFormula.cofiniteNormalForm ys)))
          LetterlessFormula.top := by
      simpa [LetterlessFormula.top, LetterlessFormula.neg] using
        (Provable.eqv_neg hcof)
    simpa [hmem] using (Provable.eqv_trans h₁ hneg)
  · have hcof :
        Provable.Eqv
          (LetterlessFormula.conj
            (LetterlessFormula.pulseAt n)
            (LetterlessFormula.cofiniteNormalForm ys))
          (LetterlessFormula.pulseAt n) := by
      simpa [hmem] using eqv_conj_pulse_cofiniteNormalForm n ys
    have hpulse :
        Provable.Eqv
          (LetterlessFormula.neg
            (LetterlessFormula.conj
              (LetterlessFormula.pulseAt n)
              (LetterlessFormula.cofiniteNormalForm ys)))
          (LetterlessFormula.neg (LetterlessFormula.pulseAt n)) :=
      Provable.eqv_neg hcof
    have hsingle :
        Provable.Eqv (LetterlessFormula.neg (LetterlessFormula.pulseAt n))
          (LetterlessFormula.cofiniteNormalForm [n]) := by
      exact Provable.eqv_trans (Provable.eqv_neg (eqv_pulseAt_singleton n))
        (by simpa using (Provable.eqv_refl (LetterlessFormula.cofiniteNormalForm [n])))
    simpa [hmem] using (Provable.eqv_trans h₁ (Provable.eqv_trans hpulse hsingle))

/--
Implication out of a derived disjunction splits as a conjunction.
-/
theorem eqv_imp_disj_left (a b c : LetterlessFormula) :
    Provable.Eqv
      (LetterlessFormula.imp (LetterlessFormula.disj a b) c)
      (LetterlessFormula.conj (a ⇒ c) (b ⇒ c)) := by
  constructor
  · have ha :
        Provable ((LetterlessFormula.disj a b ⇒ c) ⇒ (a ⇒ c)) :=
      Provable.imp_postcompose (Provable.disj_intro_left a b)
    have hb :
        Provable ((LetterlessFormula.disj a b ⇒ c) ⇒ (b ⇒ c)) :=
      Provable.imp_postcompose (Provable.disj_intro_right a b)
    exact Provable.conj_intro _ _ _ ha hb
  · have ha : Provable (LetterlessFormula.conj (a ⇒ c) (b ⇒ c) ⇒ (a ⇒ c)) :=
      Provable.conj_elim_left _ _
    have hb : Provable (LetterlessFormula.conj (a ⇒ c) (b ⇒ c) ⇒ (b ⇒ c)) :=
      Provable.conj_elim_right _ _
    let H := LetterlessFormula.conj (a ⇒ c) (b ⇒ c)
    have ha' : Provable (a ⇒ (H ⇒ c)) := by
      exact Provable.modusPonens (Provable.imp_swap H a c) ha
    have hb' : Provable (b ⇒ (H ⇒ c)) := by
      exact Provable.modusPonens (Provable.imp_swap H b c) hb
    have hdisj' : Provable (LetterlessFormula.disj a b ⇒ (H ⇒ c)) :=
      Provable.disj_elim ha' hb'
    exact Provable.modusPonens (Provable.imp_swap (LetterlessFormula.disj a b) H c) hdisj'

/--
The `finite → finite` implication case.
-/
theorem eqv_imp_finite_finite :
    ∀ xs ys : List Nat,
      Provable.Eqv (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula
        ((NormalForm.finite xs).toFormula ⇒ (NormalForm.finite ys).toFormula)
  | [], ys => by
      have hprov : Provable (LetterlessFormula.finiteNormalForm [] ⇒ LetterlessFormula.finiteNormalForm ys) :=
        Provable.ex_falso _
      simpa [NormalForm.imp, NormalForm.toFormula, LetterlessFormula.finiteNormalForm,
        LetterlessFormula.cofiniteNormalForm, LetterlessFormula.top, LetterlessFormula.neg]
        using (Provable.eqv_symm (eqv_of_provable hprov))
  | x :: xs, ys => by
      have hsplit :
          Provable.Eqv
            ((NormalForm.finite (x :: xs)).toFormula ⇒ (NormalForm.finite ys).toFormula)
            (LetterlessFormula.conj
              (LetterlessFormula.imp (LetterlessFormula.pulseAt x) (LetterlessFormula.finiteNormalForm ys))
              ((NormalForm.finite xs).toFormula ⇒ (NormalForm.finite ys).toFormula)) := by
        simpa [NormalForm.toFormula, LetterlessFormula.finiteNormalForm] using
          eqv_imp_disj_left
            (LetterlessFormula.pulseAt x)
            (LetterlessFormula.finiteNormalForm xs)
            (LetterlessFormula.finiteNormalForm ys)
      have hrest :
          Provable.Eqv
            ((NormalForm.finite xs).toFormula ⇒ (NormalForm.finite ys).toFormula)
            (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula :=
        Provable.eqv_symm (eqv_imp_finite_finite xs ys)
      by_cases hmem : x ∈ ys
      · have hpulse :
            Provable.Eqv
              (LetterlessFormula.imp (LetterlessFormula.pulseAt x) (LetterlessFormula.finiteNormalForm ys))
              LetterlessFormula.top := by
          simpa [hmem] using eqv_imp_pulse_finiteNormalForm x ys
        have hconj :
            Provable.Eqv
              (LetterlessFormula.conj
                (LetterlessFormula.imp (LetterlessFormula.pulseAt x) (LetterlessFormula.finiteNormalForm ys))
                ((NormalForm.finite xs).toFormula ⇒ (NormalForm.finite ys).toFormula))
              (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula := by
          exact Provable.eqv_trans (Provable.eqv_conj hpulse hrest) (eqv_conj_top_left _)
        have htail :
            Provable.Eqv
              ((NormalForm.finite (x :: xs)).toFormula ⇒ (NormalForm.finite ys).toFormula)
              (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula :=
          Provable.eqv_trans hsplit hconj
        exact Provable.eqv_trans
          (by simpa [NormalForm.imp, NormalForm.toFormula, NormalForm.diff, hmem] using
            (Provable.eqv_refl ((NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula)))
          (Provable.eqv_symm htail)
      · have hpulse :
            Provable.Eqv
              (LetterlessFormula.imp (LetterlessFormula.pulseAt x) (LetterlessFormula.finiteNormalForm ys))
              (LetterlessFormula.cofiniteNormalForm [x]) := by
          simpa [hmem] using eqv_imp_pulse_finiteNormalForm x ys
        have hconj :
            Provable.Eqv
              (LetterlessFormula.conj
                (LetterlessFormula.imp (LetterlessFormula.pulseAt x) (LetterlessFormula.finiteNormalForm ys))
                ((NormalForm.finite xs).toFormula ⇒ (NormalForm.finite ys).toFormula))
              (LetterlessFormula.conj
                (LetterlessFormula.cofiniteNormalForm [x])
                (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula) :=
          Provable.eqv_conj hpulse hrest
        have hcollapse :
            Provable.Eqv
              (LetterlessFormula.conj
                (LetterlessFormula.cofiniteNormalForm [x])
                (NormalForm.imp (NormalForm.finite xs) (NormalForm.finite ys)).toFormula)
              (NormalForm.imp (NormalForm.finite (x :: xs)) (NormalForm.finite ys)).toFormula := by
          exact Provable.eqv_trans
            (Provable.eqv_conj_cofiniteNormalForm_cons x (NormalForm.diff xs ys))
            (by
              simpa [NormalForm.imp, NormalForm.toFormula, NormalForm.diff, hmem] using
                (Provable.eqv_refl
                  (LetterlessFormula.cofiniteNormalForm (x :: NormalForm.diff xs ys))))
        exact Provable.eqv_symm
          (Provable.eqv_trans hsplit (Provable.eqv_trans hconj hcollapse))

/--
Proof-theoretic correctness of explicit normal-form implication.
-/
theorem eqv_imp_normalForm :
    ∀ p q : NormalForm,
      Provable.Eqv (NormalForm.imp p q).toFormula (p.toFormula ⇒ q.toFormula) :=
  eqv_imp_of_finite_core
    eqv_imp_finite_finite
    eqv_conj_finiteNormalForm

/--
If the subformulas are already provably equivalent to their recursive normal
forms, then an implication with initial-segment semantics is provably
equivalent to the corresponding iterated-bottom formula.
-/
theorem eqv_initialSegment_imp_of_subformula_normalization
    (a b : LetterlessFormula) (n : Nat)
    (ha : Provable.Eqv a (normalize a).toFormula)
    (hb : Provable.Eqv b (normalize b).toFormula)
    (h :
      LetterlessFormula.eval (a ⇒ b) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv (a ⇒ b) (LetterlessFormula.iterBoxBottom n) := by
  rcases normalize_imp_case_of_eval_eq_iterBoxBottom a b n h with
    ⟨xs, ys, hpa, hqb⟩
  have himpNorm :
      Provable.Eqv
        (a ⇒ b)
        (NormalForm.imp (normalize a) (normalize b)).toFormula := by
    have hstep :
        Provable.Eqv
          (a ⇒ b)
          ((normalize a).toFormula ⇒ (normalize b).toFormula) :=
      Provable.eqv_imp ha hb
    exact Provable.eqv_trans hstep
      (Provable.eqv_symm (eqv_imp_normalForm (normalize a) (normalize b)))
  have hfinite :
      Provable.Eqv
        (NormalForm.imp (normalize a) (normalize b)).toFormula
        (LetterlessFormula.finiteNormalForm (xs ++ ys)) := by
    simpa [hpa, hqb, NormalForm.imp, NormalForm.toFormula] using
      (Provable.eqv_refl
        (LetterlessFormula.finiteNormalForm (xs ++ ys)))
  have hevalFinite :
      LetterlessFormula.eval (LetterlessFormula.finiteNormalForm (xs ++ ys)) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) :=
    normalize_imp_cofinite_finite_eval_eq_iterBoxBottom a b n xs ys hpa hqb h
  exact Provable.eqv_trans himpNorm
    (Provable.eqv_trans hfinite
      (eqv_finiteNormalForm_of_eval_eq_iterBoxBottom (xs ++ ys) n hevalFinite))

/--
For the implication initial-segment case, it is enough to know normalization
for formulas whose recursive normal forms are respectively cofinite and finite.
-/
theorem eqv_initialSegment_imp_of_shape_normalization
    (hcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (normalize a).toFormula)
    (hfin : ∀ b : LetterlessFormula, ∀ ys : List Nat,
      normalize b = NormalForm.finite ys →
      Provable.Eqv b (normalize b).toFormula)
    (a b : LetterlessFormula) (n : Nat)
    (h :
      LetterlessFormula.eval (a ⇒ b) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv (a ⇒ b) (LetterlessFormula.iterBoxBottom n) := by
  rcases normalize_imp_case_of_eval_eq_iterBoxBottom a b n h with ⟨xs, ys, hpa, hqb⟩
  exact eqv_initialSegment_imp_of_subformula_normalization a b n
    (hcof a xs hpa)
    (hfin b ys hqb)
    h


/--
With implication settled, proof-theoretic correctness of the recursive
normalizer reduces entirely to the normal-form box operation.
-/
theorem eqv_normalize_of_box
    (hbox : ∀ p : NormalForm,
      Provable.Eqv (p.box).toFormula (□(p.toFormula))) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_ops eqv_imp_normalForm hbox

/--
If the finite and cofinite box cases are proved separately, the full recursive
normalization theorem follows immediately.
-/
theorem eqv_normalize_of_box_cases
    (hfin : ∀ xs : List Nat,
      Provable.Eqv (NormalForm.box (NormalForm.finite xs)).toFormula
        (□((NormalForm.finite xs).toFormula)))
    (hcof : ∀ xs : List Nat,
      Provable.Eqv (NormalForm.box (NormalForm.cofinite xs)).toFormula
        (□((NormalForm.cofinite xs).toFormula))) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_box (eqv_box_of_cases hfin hcof)

/--
Final reduction for the remaining completeness proof: it is enough to produce
canonical boxed representatives for finite and cofinite normal forms.
-/
theorem eqv_normalize_of_canonical_box_representatives
    (hfin : ∀ xs : List Nat, ∃ n,
      Provable.Eqv (□((NormalForm.finite xs).toFormula))
        (LetterlessFormula.iterBoxBottom n))
    (hcof : ∀ xs : List Nat,
      Provable.Eqv (□((NormalForm.cofinite xs).toFormula)) LetterlessFormula.top
      ∨ ∃ n, Provable.Eqv (□((NormalForm.cofinite xs).toFormula))
          (LetterlessFormula.iterBoxBottom n)) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_box_cases
    (eqv_box_finite_of_iterBoxBottom hfin)
    (eqv_box_cofinite_of_canonical hcof)

/--
Final endgame reduction: the remaining completeness proof is exactly the pair
of bridge theorems for boxed finite and nonempty boxed cofinite normal forms.
-/
theorem eqv_normalize_of_box_bridges
    (hfin : ∀ xs : List Nat, ∃ n,
      Provable.Eqv (□((NormalForm.finite xs).toFormula))
        (LetterlessFormula.iterBoxBottom n))
    (hcof : ∀ xs : List Nat, xs ≠ [] →
      Provable.Eqv
        (□((NormalForm.cofinite xs).toFormula))
        (LetterlessFormula.iterBoxBottom (minList xs + 1))) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_canonical_box_representatives
    hfin
    (fun xs =>
      by
        by_cases hxs : xs = []
        · left
          simpa [hxs] using eqv_box_formula_cofinite_nil
        · right
          exact ⟨minList xs + 1, hcof xs hxs⟩)

/--
Final reduction in a more conceptual form: it is enough to prove a single
bridge theorem saying that if a letterless formula has a first false time `n`,
then boxing it yields `□^(n+1)⊥`.
-/
theorem eqv_normalize_of_first_false_bridge
    (hff : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_box_bridges
    (fun xs => by
      have hex :
          ∃ t, LetterlessFormula.eval ((NormalForm.finite xs).toFormula) t = false := by
        refine ⟨succAbove xs, ?_⟩
        rw [NormalForm.toFormula, LetterlessFormula.eval_finiteNormalForm]
        simp [not_mem_succAbove]
      let ff := firstFalseOfExistsFalse
          (LetterlessFormula.eval ((NormalForm.finite xs).toFormula)) hex
      exact ⟨ff.idx + 1,
        hff ((NormalForm.finite xs).toFormula) ff.idx ff.false_at ff.before_true⟩)
    (fun xs hxs => by
      have hfalse :
          LetterlessFormula.eval ((NormalForm.cofinite xs).toFormula) (minList xs) = false := by
        rw [NormalForm.toFormula, LetterlessFormula.eval_cofiniteNormalForm]
        simp [minList_mem_of_ne_nil hxs]
      have hbefore :
          ∀ k, k < minList xs →
            LetterlessFormula.eval ((NormalForm.cofinite xs).toFormula) k = true := by
        intro k hk
        rw [NormalForm.toFormula, LetterlessFormula.eval_cofiniteNormalForm]
        simp [not_mem_of_lt_minList hxs hk]
      simpa using hff ((NormalForm.cofinite xs).toFormula) (minList xs) hfalse hbefore)

/--
The first-false bridge itself reduces to a semantic extensionality principle:
if semantic equality of letterless formulas implies provable equivalence, then
the boxed formula is equivalent to the corresponding iterated bottom.
-/
theorem first_false_bridge_of_semantic_extensionality
    (hext : ∀ a b : LetterlessFormula,
      LetterlessFormula.eval a = LetterlessFormula.eval b →
      Provable.Eqv a b) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1)) := by
  intro a n hnfalse hbefore
  apply hext
  funext t
  cases ht : LetterlessFormula.eval (□a) t with
  | false =>
      have hnotlt : ¬ t < n + 1 := by
        intro hlt
        have htrue : LetterlessFormula.eval (□a) t = true := by
          rw [LetterlessFormula.eval_box]
          apply (Bitstream.box_eq_true_iff_prefix_all_true _ t).2
          intro j hj
          exact hbefore j (Nat.lt_of_lt_of_le hj (Nat.le_of_lt_succ hlt))
        simp [htrue] at ht
      have hfalse' : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) t = false := by
        cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) t with
        | false => exact rfl
        | true =>
            exact False.elim (hnotlt ((LetterlessFormula.eval_iterBoxBottom_true_iff (n + 1) t).1 hval))
      simp [hfalse']
  | true =>
      have hlt : t < n + 1 := by
        rw [LetterlessFormula.eval_box] at ht
        cases t with
        | zero =>
            simp
        | succ t =>
            have hall : ∀ j, j < Nat.succ t → LetterlessFormula.eval a j = true := by
              exact (Bitstream.box_eq_true_iff_prefix_all_true _ (Nat.succ t)).1 ht
            have htn : t < n := by
              have := hall t (Nat.lt_succ_self t)
              by_cases hbad : n ≤ t
              · have hcontra : LetterlessFormula.eval a n = true := hall n (Nat.lt_of_le_of_lt hbad (Nat.lt_succ_self t))
                simp [hnfalse] at hcontra
              · exact Nat.lt_of_not_ge hbad
            simpa using Nat.succ_lt_succ htn
      have htrue' :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) t = true :=
        (LetterlessFormula.eval_iterBoxBottom_true_iff (n + 1) t).2 hlt
      simp [htrue']

/--
Semantic form of the first-false bridge: if `a` is true at all times `< n` and
false at `n`, then `□a` has exactly the denotation of `□^(n+1)⊥`.
-/
theorem eval_box_eq_iterBoxBottom_of_first_false
    (a : LetterlessFormula) (n : Nat)
    (hnfalse : LetterlessFormula.eval a n = false)
    (hbefore : ∀ k, k < n → LetterlessFormula.eval a k = true) :
    LetterlessFormula.eval (□a) =
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := by
  funext t
  cases ht : LetterlessFormula.eval (□a) t with
  | false =>
      have hnotlt : ¬ t < n + 1 := by
        intro hlt
        have htrue : LetterlessFormula.eval (□a) t = true := by
          rw [LetterlessFormula.eval_box]
          apply (Bitstream.box_eq_true_iff_prefix_all_true _ t).2
          intro j hj
          exact hbefore j (Nat.lt_of_lt_of_le hj (Nat.le_of_lt_succ hlt))
        simp [htrue] at ht
      have hfalse' : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) t = false := by
        cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) t with
        | false => exact rfl
        | true =>
            exact False.elim (hnotlt ((LetterlessFormula.eval_iterBoxBottom_true_iff (n + 1) t).1 hval))
      simp [hfalse']
  | true =>
      have hlt : t < n + 1 := by
        rw [LetterlessFormula.eval_box] at ht
        cases t with
        | zero =>
            simp
        | succ t =>
            have hall : ∀ j, j < Nat.succ t → LetterlessFormula.eval a j = true := by
              exact (Bitstream.box_eq_true_iff_prefix_all_true _ (Nat.succ t)).1 ht
            have htn : t < n := by
              have := hall t (Nat.lt_succ_self t)
              by_cases hbad : n ≤ t
              · have hcontra : LetterlessFormula.eval a n = true := hall n (Nat.lt_of_le_of_lt hbad (Nat.lt_succ_self t))
                simp [hnfalse] at hcontra
              · exact Nat.lt_of_not_ge hbad
            simpa using Nat.succ_lt_succ htn
      have htrue' :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) t = true :=
        (LetterlessFormula.eval_iterBoxBottom_true_iff (n + 1) t).2 hlt
      simp [htrue']

/--
Restated semantically, the `box` initial-segment case is exactly the first-false
bridge for the inner formula.
-/
theorem eqv_initialSegment_box_of_first_false
    (a : LetterlessFormula) (n : Nat)
    (hnfalse : LetterlessFormula.eval a n = false)
    (hbefore : ∀ k, k < n → LetterlessFormula.eval a k = true) :
    Provable.Eqv (□a) (normalize (□a)).toFormula ↔
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1)) := by
  have h :
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) :=
    eval_box_eq_iterBoxBottom_of_first_false a n hnfalse hbefore
  exact eqv_initialSegment_box_iff_iterBoxBottom a (n + 1) h

/--
A boxed formula can never denote `⊥`, since `□a` is always true at time `0`.
-/
theorem eval_box_ne_iterBoxBottom_zero (a : LetterlessFormula) :
    LetterlessFormula.eval (□a) ≠
      LetterlessFormula.eval (LetterlessFormula.iterBoxBottom 0) := by
  intro h
  have hbox0 : LetterlessFormula.eval (□a) 0 = true := by
    rw [LetterlessFormula.eval_box]
    rfl
  have hiter0 : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom 0) 0 = false := by
    simp [LetterlessFormula.eval_iterBoxBottom]
  have hcontra := congrArg (fun f => f 0) h
  simp [hbox0, hiter0] at hcontra

/--
If `□a` denotes `□^(n+1)⊥`, then `a` is true at all times `< n` and false at
time `n`.
-/
theorem first_false_of_eval_box_eq_iterBoxBottom_succ
    (a : LetterlessFormula) (n : Nat)
    (h :
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1))) :
    LetterlessFormula.eval a n = false ∧
      (∀ k, k < n → LetterlessFormula.eval a k = true) := by
  have hboxtrue :
      LetterlessFormula.eval (□a) n = true := by
    have :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) n = true :=
      (LetterlessFormula.eval_iterBoxBottom_true_iff (n + 1) n).2 (Nat.lt_succ_self n)
    simpa [this] using congrArg (fun f => f n) h
  have hboxfalse :
      LetterlessFormula.eval (□a) (n + 1) = false := by
    have :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) (n + 1) = false := by
      cases hval : LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) (n + 1) with
      | false => exact rfl
      | true =>
          exact False.elim
            (Nat.lt_irrefl (n + 1)
              ((LetterlessFormula.eval_iterBoxBottom_true_iff (n + 1) (n + 1)).1 hval))
    simpa [this] using congrArg (fun f => f (n + 1)) h
  have hbefore :
      ∀ k, k < n → LetterlessFormula.eval a k = true := by
    intro k hk
    rw [LetterlessFormula.eval_box] at hboxtrue
    exact (Bitstream.box_eq_true_iff_prefix_all_true _ n).1 hboxtrue k hk
  have hnfalse :
      LetterlessFormula.eval a n = false := by
    rw [LetterlessFormula.eval_box] at hboxtrue hboxfalse
    rw [Bitstream.box_succ, hboxtrue] at hboxfalse
    simpa using hboxfalse
  exact ⟨hnfalse, hbefore⟩

/--
The first-false bridge only needs semantic extensionality against iterated
bottom formulas, not full extensionality between arbitrary formulas.
-/
theorem first_false_bridge_of_box_iter_extensionality
    (hext : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv a (LetterlessFormula.iterBoxBottom n)) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1)) := by
  intro a n hnfalse hbefore
  exact hext (□a) (n + 1)
    (eval_box_eq_iterBoxBottom_of_first_false a n hnfalse hbefore)

/--
The `box` initial-segment case follows directly from the first-false bridge.
-/
theorem eqv_initialSegment_box_of_bridge
    (hff : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (normalize (□a)).toFormula
  | a, 0, h => by
      exact False.elim (eval_box_ne_iterBoxBottom_zero a h)
  | a, n + 1, h => by
      rcases first_false_of_eval_box_eq_iterBoxBottom_succ a n h with ⟨hnfalse, hbefore⟩
      exact (eqv_initialSegment_box_of_first_false a n hnfalse hbefore).2
        (hff a n hnfalse hbefore)

/--
If semantic equality implies provable equivalence for letterless formulas, then
the full recursive normalization theorem follows.
-/
theorem eqv_normalize_of_semantic_extensionality
    (hext : ∀ a b : LetterlessFormula,
      LetterlessFormula.eval a = LetterlessFormula.eval b →
      Provable.Eqv a b) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_first_false_bridge
    (first_false_bridge_of_semantic_extensionality hext)

/--
Even more specifically, completeness reduces to extensionality only for
letterless formulas whose denotation is an initial segment.
-/
theorem eqv_normalize_of_box_iter_extensionality
    (hext : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv a (LetterlessFormula.iterBoxBottom n)) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_first_false_bridge
    (first_false_bridge_of_box_iter_extensionality hext)

/--
It is enough to prove that every letterless formula is provably equivalent to
its chosen normal form in the special case where that normal form denotes an
initial segment.
-/
theorem eqv_normalize_of_initialSegment_normalForm
    (hnf : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv a (normalFormOf a).toFormula) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_box_iter_extensionality
    (fun a n h =>
      eqv_of_eval_eq_iterBoxBottom_and_normalForm a n (hnf a n h) h)

/--
An even closer endgame: it is enough to show that whenever a letterless formula
denotes an initial segment, it is provably equivalent to its recursive normal
form `normalize a`.
-/
theorem eqv_normalize_of_initialSegment_recursive
    (hnorm : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv a (normalize a).toFormula) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_box_iter_extensionality
    (fun a n h =>
      eqv_of_eval_eq_iterBoxBottom_and_normalize a n (hnorm a n h) h)

/--
Since the `box` branch is already controlled by the first-false bridge, the
remaining initial-segment normalization problem reduces entirely to the
implication branch.
-/
theorem eqv_initialSegment_recursive_of_imp_case_and_first_false_bridge
    (himp : ∀ a b : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (a ⇒ b) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (a ⇒ b) (LetterlessFormula.iterBoxBottom n))
    (hff : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv a (normalize a).toFormula :=
  eqv_initialSegment_recursive_of_iter_cases
    himp
    (fun a n h =>
      (eqv_initialSegment_box_iff_iterBoxBottom a n h).1
        (eqv_initialSegment_box_of_bridge hff a n h))

/--
Combining the implication-shape reduction with the first-false bridge, initial-
segment recursive normalization reduces to two normalization problems:
formulas whose recursive normal forms are explicitly finite or explicitly
cofinite.
-/
theorem eqv_initialSegment_recursive_of_shape_normalization_and_first_false
    (hcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (normalize a).toFormula)
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (normalize a).toFormula)
    (hff : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv a (normalize a).toFormula :=
  eqv_initialSegment_recursive_of_imp_case_and_first_false_bridge
    (eqv_initialSegment_imp_of_shape_normalization hcof hfin)
    hff

/--
Therefore full recursive normalization follows from finite/cofinite recursive
normalization together with the first-false bridge.
-/
theorem eqv_normalize_of_shape_normalization_and_first_false
    (hcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (normalize a).toFormula)
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (normalize a).toFormula)
    (hff : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_initialSegment_recursive
    (eqv_initialSegment_recursive_of_shape_normalization_and_first_false hcof hfin hff)

/--
Since `normalize a = finite ys` means `(normalize a).toFormula` is literally
`finiteNormalForm ys`, finite-shape normalization can be stated directly using
that canonical formula.
-/
theorem eqv_normalize_of_explicit_shape_normalization_and_first_false
    (hcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs))
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys))
    (hff : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a := by
  apply eqv_normalize_of_shape_normalization_and_first_false
  · intro a xs hxs
    simpa [hxs, NormalForm.toFormula] using hcof a xs hxs
  · intro a ys hys
    simpa [hys, NormalForm.toFormula] using hfin a ys hys
  · exact hff

/--
Final statement of the remaining completeness obligations: it is enough to show
that any formula whose recursive normal form is explicitly finite or explicitly
cofinite is provably equivalent to that explicit normal form, together with the
first-false bridge for `□`.
-/
theorem completeness_reduces_to_explicit_shape_normalization
    (hcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs))
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys))
    (hff : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  eqv_normalize_of_explicit_shape_normalization_and_first_false hcof hfin hff

/--
The first-false bridge itself follows from finite-shape normalization, since
the recursive normal form of `□a` must be finite whenever `□a` denotes an
initial segment.
-/
theorem first_false_bridge_of_finite_shape_normalization
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys)) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1)) := by
  intro a n hnfalse hbefore
  have hbox :
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) :=
    eval_box_eq_iterBoxBottom_of_first_false a n hnfalse hbefore
  rcases exists_finite_shape_of_eval_eq_iterBoxBottom (normalize (□a)) (n + 1) (by
      calc
        LetterlessFormula.eval (normalize (□a)).toFormula = LetterlessFormula.eval (□a) :=
          eval_normalize (□a)
        _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := hbox) with
    ⟨ys, hys⟩
  have hshape :
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys) :=
    hfin (□a) ys hys
  have hevalFinite :
      LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := by
    calc
      LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
        LetterlessFormula.eval (normalize (□a)).toFormula := by
          simp [hys, NormalForm.toFormula]
      _ = LetterlessFormula.eval (□a) := eval_normalize (□a)
      _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := hbox
  exact Provable.eqv_trans hshape
    (eqv_finiteNormalForm_of_eval_eq_iterBoxBottom ys (n + 1) hevalFinite)

/--
So the full recursive normalization theorem ultimately reduces to just the two
explicit-shape normalization statements, finite and cofinite.
-/
theorem completeness_reduces_to_explicit_shape_normalization_only
    (hcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs))
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys)) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  completeness_reduces_to_explicit_shape_normalization
    hcof
    hfin
    (first_false_bridge_of_finite_shape_normalization hfin)

/--
The cofinite-shape normalization theorem follows from the finite-shape one by
applying it to `¬a`.
-/
theorem cofinite_shape_normalization_of_finite
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys)) :
    ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs) := by
  intro a xs hax
  have hnegNorm :
      normalize (LetterlessFormula.neg a) = NormalForm.finite xs := by
    simp [LetterlessFormula.neg, normalize, hax, NormalForm.imp]
  have hneg :
      Provable.Eqv (LetterlessFormula.neg a) (LetterlessFormula.finiteNormalForm xs) :=
    hfin (LetterlessFormula.neg a) xs hnegNorm
  have hnegneg :
      Provable.Eqv (LetterlessFormula.neg (LetterlessFormula.neg a))
        (LetterlessFormula.neg (LetterlessFormula.finiteNormalForm xs)) :=
    Provable.eqv_neg hneg
  exact Provable.eqv_trans
    (Provable.eqv_doubleNeg a)
    (by simpa [LetterlessFormula.cofiniteNormalForm] using hnegneg)

/--
No finite normal form denotes `⊤`.
-/
theorem eval_finiteNormalForm_ne_top (ys : List Nat) :
    LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) ≠
      LetterlessFormula.eval LetterlessFormula.top := by
  intro h
  exact eval_finiteNormalForm_ne_cofiniteNormalForm ys [] (by
    simpa [LetterlessFormula.cofiniteNormalForm, LetterlessFormula.top] using h)

/--
If `□a` denotes `⊤`, then `a` itself denotes `⊤`.
-/
theorem eval_eq_top_of_eval_box_eq_top (a : LetterlessFormula)
    (h :
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval LetterlessFormula.top) :
    LetterlessFormula.eval a =
      LetterlessFormula.eval LetterlessFormula.top := by
  funext t
  have hbox :
      LetterlessFormula.eval (□a) (t + 1) = true := by
    have hpt := congrArg (fun f => f (t + 1)) h
    simpa [LetterlessFormula.eval_top, const1, const] using hpt
  have ha : LetterlessFormula.eval a t = true := by
    rw [LetterlessFormula.eval_box] at hbox
    exact (Bitstream.box_eq_true_iff_prefix_all_true _ (t + 1)).1 hbox t (Nat.lt_succ_self t)
  simp [LetterlessFormula.eval_top, const1, const, ha]

/--
If a cofinite normal form denotes `⊤`, it is provably equivalent to `⊤`.
-/
theorem eqv_cofiniteNormalForm_of_eval_eq_top
    (xs : List Nat)
    (h :
      LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) =
        LetterlessFormula.eval LetterlessFormula.top) :
    Provable.Eqv (LetterlessFormula.cofiniteNormalForm xs) LetterlessFormula.top := by
  have hcof :
      LetterlessFormula.eval (NormalForm.cofinite xs).toFormula =
        LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm []) := by
    simpa [NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm, LetterlessFormula.top] using h
  exact Provable.eqv_trans
    (eqv_normalForm_of_eval_eq_cofiniteNormalForm (NormalForm.cofinite xs) [] hcof)
    eqv_cofinite_nil_top

/--
Given shape normalization for the inner formula `a`, the cofinite boxed case
follows automatically: the only possible cofinite denotation of `□a` is `⊤`.
-/
theorem box_cofinite_shape_of_subformula_shapes
    (a : LetterlessFormula)
    (hacof : ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs)) :
    ∀ xs : List Nat,
      normalize (□a) = NormalForm.cofinite xs →
      Provable.Eqv (□a) (LetterlessFormula.cofiniteNormalForm xs) := by
  intro xs hxs
  have hboxEval :
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) := by
    calc
      LetterlessFormula.eval (□a) = LetterlessFormula.eval (normalize (□a)).toFormula :=
        (eval_normalize (□a)).symm
      _ = LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) := by
        simp [hxs, NormalForm.toFormula]
  have htopBox :
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval LetterlessFormula.top := by
    rcases box_all_true_or_exists_firstFalse (LetterlessFormula.eval a) with hconst | ⟨ff, -⟩
    · simpa [LetterlessFormula.eval_box, LetterlessFormula.eval_top] using hconst
    · have hiter :
          LetterlessFormula.eval (□a) =
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom ff.idx) := by
        simpa [LetterlessFormula.eval_box] using
          (eval_box_eq_iterBoxBottom_of_box_firstFalse
            (LetterlessFormula.eval a) ff)
      exact False.elim
        (eval_cofiniteNormalForm_ne_iterBoxBottom xs ff.idx (Eq.trans hboxEval.symm hiter))
  have htopA :
      LetterlessFormula.eval a =
        LetterlessFormula.eval LetterlessFormula.top :=
    eval_eq_top_of_eval_box_eq_top a htopBox
  cases hna : normalize a with
  | finite ys =>
      exfalso
      have hfinEval :
          LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
            LetterlessFormula.eval LetterlessFormula.top := by
        calc
          LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
            LetterlessFormula.eval (normalize a).toFormula := by
              simp [hna, NormalForm.toFormula]
          _ = LetterlessFormula.eval a := eval_normalize a
          _ = LetterlessFormula.eval LetterlessFormula.top := htopA
      exact eval_finiteNormalForm_ne_top ys hfinEval
  | cofinite ys =>
      have ha :
          Provable.Eqv a (LetterlessFormula.cofiniteNormalForm ys) :=
        hacof ys hna
      have hyTop :
          Provable.Eqv (LetterlessFormula.cofiniteNormalForm ys) LetterlessFormula.top := by
        have hyEval :
            LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm ys) =
              LetterlessFormula.eval LetterlessFormula.top := by
          calc
            LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm ys) =
              LetterlessFormula.eval (normalize a).toFormula := by
                simp [hna, NormalForm.toFormula]
            _ = LetterlessFormula.eval a := eval_normalize a
            _ = LetterlessFormula.eval LetterlessFormula.top := htopA
        exact eqv_cofiniteNormalForm_of_eval_eq_top ys hyEval
      have hboxTop : Provable.Eqv (□a) LetterlessFormula.top := by
        exact Provable.eqv_trans
          (Provable.eqv_box (Provable.eqv_trans ha hyTop))
          eqv_box_top
      have hxEvalTop :
          LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) =
            LetterlessFormula.eval LetterlessFormula.top := by
        exact Eq.trans hboxEval.symm htopBox
      have hxTop :
          Provable.Eqv LetterlessFormula.top (LetterlessFormula.cofiniteNormalForm xs) := by
        exact Provable.eqv_symm (eqv_cofiniteNormalForm_of_eval_eq_top xs hxEvalTop)
      exact Provable.eqv_trans hboxTop hxTop

/--
So the full recursive normalization theorem ultimately reduces to the finite
explicit-shape normalization statement alone.
-/
theorem completeness_reduces_to_finite_shape_normalization_only
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys)) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  completeness_reduces_to_explicit_shape_normalization_only
    (cofinite_shape_normalization_of_finite hfin)
    hfin

/--
If finite/cofinite shape normalization is known for boxed formulas, then it
follows for all formulas by structural induction.
-/
theorem explicit_shape_normalization_of_box_shapes
    (hbfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize (□a) = NormalForm.finite ys →
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys))
    (hbcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize (□a) = NormalForm.cofinite xs →
      Provable.Eqv (□a) (LetterlessFormula.cofiniteNormalForm xs)) :
    ∀ a : LetterlessFormula,
      (∀ ys : List Nat,
        normalize a = NormalForm.finite ys →
        Provable.Eqv a (LetterlessFormula.finiteNormalForm ys)) ∧
      (∀ xs : List Nat,
        normalize a = NormalForm.cofinite xs →
        Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs)) := by
  intro a
  induction a with
  | bottom =>
      constructor
      · intro ys hys
        have hnil : ys = [] := by
          simpa [normalize] using hys
        simpa [hnil, LetterlessFormula.finiteNormalForm] using
          (Provable.eqv_refl (⊥ : LetterlessFormula))
      · intro xs hxs
        cases hxs
  | imp a b iha ihb =>
      rcases iha with ⟨ihafin, ihacof⟩
      rcases ihb with ⟨ihbfin, ihbcof⟩
      constructor
      · intro ys hys
        cases hna : normalize a with
        | finite as =>
            cases hnb : normalize b with
            | finite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hys
            | cofinite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hys
        | cofinite as =>
            cases hnb : normalize b with
            | cofinite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hys
            | finite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.cofiniteNormalForm as) :=
                  ihacof as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.finiteNormalForm bs) :=
                  ihbfin bs hnb
                have hlist : ys = as ++ bs := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hys.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.cofinite as) (NormalForm.finite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.cofinite as) (NormalForm.finite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
      · intro xs hxs
        cases hna : normalize a with
        | finite as =>
            cases hnb : normalize b with
            | finite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.finiteNormalForm as) :=
                  ihafin as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.finiteNormalForm bs) :=
                  ihbfin bs hnb
                have hlist : xs = NormalForm.diff as bs := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hxs.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.finite as) (NormalForm.finite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.finite as) (NormalForm.finite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
            | cofinite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.finiteNormalForm as) :=
                  ihafin as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.cofiniteNormalForm bs) :=
                  ihbcof bs hnb
                have hlist : xs = NormalForm.inter as bs := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hxs.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.finite as) (NormalForm.cofinite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.finite as) (NormalForm.cofinite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
        | cofinite as =>
            cases hnb : normalize b with
            | finite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hxs
            | cofinite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.cofiniteNormalForm as) :=
                  ihacof as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.cofiniteNormalForm bs) :=
                  ihbcof bs hnb
                have hlist : xs = NormalForm.diff bs as := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hxs.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.cofinite as) (NormalForm.cofinite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.cofinite as) (NormalForm.cofinite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
  | box a iha =>
      constructor
      · intro ys hys
        exact hbfin a ys hys
      · intro xs hxs
        exact hbcof a xs hxs

/--
Hence the remaining completeness work is concentrated entirely in boxed
formulas.
-/
theorem completeness_reduces_to_box_shape_normalization
    (hbfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize (□a) = NormalForm.finite ys →
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys))
    (hbcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize (□a) = NormalForm.cofinite xs →
      Provable.Eqv (□a) (LetterlessFormula.cofiniteNormalForm xs)) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a := by
  have hshapes := explicit_shape_normalization_of_box_shapes hbfin hbcof
  exact completeness_reduces_to_explicit_shape_normalization_only
    (fun a xs hxs => (hshapes a).2 xs hxs)
    (fun a ys hys => (hshapes a).1 ys hys)

/--
Using the boxed cofinite helper, the global shape-normalization problem reduces
further to boxed formulas whose recursive normal forms are finite.
-/
theorem explicit_shape_normalization_of_box_finite_only
    (hbfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize (□a) = NormalForm.finite ys →
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys)) :
    ∀ a : LetterlessFormula,
      (∀ ys : List Nat,
        normalize a = NormalForm.finite ys →
        Provable.Eqv a (LetterlessFormula.finiteNormalForm ys)) ∧
      (∀ xs : List Nat,
        normalize a = NormalForm.cofinite xs →
        Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs)) := by
  intro a
  induction a with
  | bottom =>
      constructor
      · intro ys hys
        have hnil : ys = [] := by
          simpa [normalize] using hys
        simpa [hnil, LetterlessFormula.finiteNormalForm] using
          (Provable.eqv_refl (⊥ : LetterlessFormula))
      · intro xs hxs
        cases hxs
  | imp a b iha ihb =>
      rcases iha with ⟨ihafin, ihacof⟩
      rcases ihb with ⟨ihbfin, ihbcof⟩
      constructor
      · intro ys hys
        cases hna : normalize a with
        | finite as =>
            cases hnb : normalize b with
            | finite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hys
            | cofinite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hys
        | cofinite as =>
            cases hnb : normalize b with
            | cofinite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hys
            | finite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.cofiniteNormalForm as) :=
                  ihacof as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.finiteNormalForm bs) :=
                  ihbfin bs hnb
                have hlist : ys = as ++ bs := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hys.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.cofinite as) (NormalForm.finite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.cofinite as) (NormalForm.finite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
      · intro xs hxs
        cases hna : normalize a with
        | finite as =>
            cases hnb : normalize b with
            | finite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.finiteNormalForm as) :=
                  ihafin as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.finiteNormalForm bs) :=
                  ihbfin bs hnb
                have hlist : xs = NormalForm.diff as bs := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hxs.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.finite as) (NormalForm.finite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.finite as) (NormalForm.finite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
            | cofinite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.finiteNormalForm as) :=
                  ihafin as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.cofiniteNormalForm bs) :=
                  ihbcof bs hnb
                have hlist : xs = NormalForm.inter as bs := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hxs.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.finite as) (NormalForm.cofinite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.finite as) (NormalForm.cofinite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
        | cofinite as =>
            cases hnb : normalize b with
            | finite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hxs
            | cofinite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.cofiniteNormalForm as) :=
                  ihacof as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.cofiniteNormalForm bs) :=
                  ihbcof bs hnb
                have hlist : xs = NormalForm.diff bs as := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hxs.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.cofinite as) (NormalForm.cofinite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.cofinite as) (NormalForm.cofinite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
  | box a iha =>
      rcases iha with ⟨ihafin, ihacof⟩
      constructor
      · intro ys hys
        exact hbfin a ys hys
      · intro xs hxs
        exact box_cofinite_shape_of_subformula_shapes a ihacof xs hxs

/--
Hence the whole completeness development now reduces to proving boxed formulas
with finite recursive normal forms are equivalent to those finite codes.
-/
theorem completeness_reduces_to_box_finite_shape_normalization
    (hbfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize (□a) = NormalForm.finite ys →
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys)) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a := by
  have hshapes := explicit_shape_normalization_of_box_finite_only hbfin
  exact completeness_reduces_to_explicit_shape_normalization_only
    (fun a xs hxs => (hshapes a).2 xs hxs)
    (fun a ys hys => (hshapes a).1 ys hys)

/--
The remaining boxed finite-shape theorem follows from the first-false bridge.
-/
theorem box_finite_shape_of_first_false_bridge
    (hff : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize (□a) = NormalForm.finite ys →
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys) := by
  intro a ys hys
  have hEvalFinite :
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) := by
    calc
      LetterlessFormula.eval (□a) = LetterlessFormula.eval (normalize (□a)).toFormula :=
        (eval_normalize (□a)).symm
      _ = LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) := by
        simp [hys, NormalForm.toFormula]
  rcases box_all_true_or_exists_firstFalse (LetterlessFormula.eval a) with hconst | ⟨ff, -⟩
  · exfalso
    have htop :
        LetterlessFormula.eval (□a) = LetterlessFormula.eval LetterlessFormula.top := by
      simpa [LetterlessFormula.eval_box, LetterlessFormula.eval_top] using hconst
    exact eval_finiteNormalForm_ne_top ys (Eq.trans hEvalFinite.symm htop)
  · have hiter :
        LetterlessFormula.eval (□a) =
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom ff.idx) := by
      simpa [LetterlessFormula.eval_box] using
        (eval_box_eq_iterBoxBottom_of_box_firstFalse
          (LetterlessFormula.eval a) ff)
    have hnpos : ff.idx ≠ 0 := by
      intro hz
      have hzero : LetterlessFormula.eval (□a) 0 = true := by
        rw [LetterlessFormula.eval_box]
        rfl
      have hfalse0 : LetterlessFormula.eval (□a) 0 = false := by
        simpa [LetterlessFormula.eval_box, hz] using ff.false_at
      rw [hzero] at hfalse0
      cases hfalse0
    rcases Nat.exists_eq_succ_of_ne_zero hnpos with ⟨m, hm⟩
    have hiterSucc :
        LetterlessFormula.eval (□a) =
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (m + 1)) := by
      simpa [hm] using hiter
    rcases first_false_of_eval_box_eq_iterBoxBottom_succ a m hiterSucc with ⟨hafalse, habefore⟩
    have hysIter :
        LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (m + 1)) := by
      exact Eq.trans hEvalFinite.symm hiterSucc
    exact Provable.eqv_trans
      (hff a m hafalse habefore)
      (Provable.eqv_symm
        (eqv_finiteNormalForm_of_eval_eq_iterBoxBottom ys (m + 1) hysIter))

/--
So the whole completeness development can again be driven by the single
first-false bridge theorem, now via the boxed finite-shape reduction.
-/
theorem completeness_reduces_to_first_false_bridge_again
    (hff : ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  completeness_reduces_to_box_finite_shape_normalization
    (box_finite_shape_of_first_false_bridge hff)

/--
Conversely, the first-false bridge follows already from the boxed finite-shape
normalization theorem.
-/
theorem first_false_bridge_of_box_finite_shape
    (hbfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize (□a) = NormalForm.finite ys →
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys)) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1)) := by
  intro a n hnfalse hbefore
  have hbox :
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) :=
    eval_box_eq_iterBoxBottom_of_first_false a n hnfalse hbefore
  rcases exists_finite_shape_of_eval_eq_iterBoxBottom (normalize (□a)) (n + 1) (by
      calc
        LetterlessFormula.eval (normalize (□a)).toFormula = LetterlessFormula.eval (□a) :=
          eval_normalize (□a)
        _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := hbox) with
    ⟨ys, hys⟩
  have hshape :
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys) :=
    hbfin a ys hys
  have hevalFinite :
      LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := by
    calc
      LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
        LetterlessFormula.eval (normalize (□a)).toFormula := by
          simp [hys, NormalForm.toFormula]
      _ = LetterlessFormula.eval (□a) := eval_normalize (□a)
      _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (n + 1)) := hbox
  exact Provable.eqv_trans hshape
    (eqv_finiteNormalForm_of_eval_eq_iterBoxBottom ys (n + 1) hevalFinite)

/--
So the boxed finite-shape theorem and the first-false bridge are equivalent
forms of the same remaining completeness obligation.
-/
theorem box_finite_shape_iff_first_false_bridge :
    (∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize (□a) = NormalForm.finite ys →
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys))
      ↔
    (∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) := by
  constructor
  · exact first_false_bridge_of_box_finite_shape
  · exact box_finite_shape_of_first_false_bridge

/--
Equivalently, the same remaining obligation can be phrased as extensionality
for boxed formulas against the initial-segment family `□^n ⊥`.
-/
theorem box_iter_extensionality_iff_first_false_bridge :
    (∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n))
      ↔
    (∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval a n = false →
      (∀ k, k < n → LetterlessFormula.eval a k = true) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom (n + 1))) := by
  constructor
  · intro hext
    intro a n hnfalse hbefore
    exact hext a (n + 1)
      (eval_box_eq_iterBoxBottom_of_first_false a n hnfalse hbefore)
  · intro hff a n h
    cases n with
    | zero =>
        exact False.elim (eval_box_ne_iterBoxBottom_zero a h)
    | succ m =>
        rcases first_false_of_eval_box_eq_iterBoxBottom_succ a m h with ⟨hnfalse, hbefore⟩
        exact hff a m hnfalse hbefore

/--
Hence boxed finite-shape normalization and boxed initial-segment extensionality
are equivalent formulations of the same remaining theorem.
-/
theorem box_finite_shape_iff_box_iter_extensionality :
    (∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize (□a) = NormalForm.finite ys →
      Provable.Eqv (□a) (LetterlessFormula.finiteNormalForm ys))
      ↔
    (∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n)) := by
  constructor
  · intro hshape
    have hff := (box_finite_shape_iff_first_false_bridge.mp hshape)
    exact box_iter_extensionality_iff_first_false_bridge.mpr hff
  · intro hext
    have hff := (box_iter_extensionality_iff_first_false_bridge.mp hext)
    exact box_finite_shape_iff_first_false_bridge.mpr hff

/--
Conversely, once full recursive normalization is available, boxed initial-
segment extensionality is immediate.
-/
theorem box_iter_extensionality_of_normalization
    (hnorm : ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n) := by
  intro a n h
  exact eqv_of_eval_eq_iterBoxBottom_and_normalize (□a) n
    (Provable.eqv_symm (hnorm (□a))) h

/--
So the remaining boxed initial-segment theorem is equivalent to the full
recursive normalization/completeness theorem.
-/
theorem normalization_iff_box_iter_extensionality :
    (∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a)
      ↔
    (∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n)) := by
  constructor
  · exact box_iter_extensionality_of_normalization
  · intro hext
    exact completeness_reduces_to_first_false_bridge_again
      ((box_iter_extensionality_iff_first_false_bridge.mp hext))

/--
To prove boxed initial-segment extensionality for arbitrary formulas, it is
enough to prove it for the explicit finite and cofinite normal-form codes.
-/
theorem box_iter_extensionality_of_explicit_box_codes
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys))
    (hcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs))
    (hboxfin : ∀ ys : List Nat, ∀ n : Nat,
      LetterlessFormula.eval (□(LetterlessFormula.finiteNormalForm ys)) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv
        (□(LetterlessFormula.finiteNormalForm ys))
        (LetterlessFormula.iterBoxBottom n))
    (hboxcof : ∀ xs : List Nat, ∀ n : Nat,
      LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv
        (□(LetterlessFormula.cofiniteNormalForm xs))
        (LetterlessFormula.iterBoxBottom n)) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n) := by
  intro a n h
  cases hna : normalize a with
  | finite ys =>
      have ha :
          Provable.Eqv a (LetterlessFormula.finiteNormalForm ys) :=
        hfin a ys hna
      have hEval :
          LetterlessFormula.eval (□(LetterlessFormula.finiteNormalForm ys)) =
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
        calc
          LetterlessFormula.eval (□(LetterlessFormula.finiteNormalForm ys)) =
            LetterlessFormula.eval (□a) := by
              exact Provable.eqv_sound (Provable.eqv_box (Provable.eqv_symm ha))
          _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
      exact Provable.eqv_trans
        (Provable.eqv_box ha)
        (hboxfin ys n hEval)
  | cofinite xs =>
      have ha :
          Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs) :=
        hcof a xs hna
      have hEval :
          LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) =
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
        calc
          LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) =
            LetterlessFormula.eval (□a) := by
              exact Provable.eqv_sound (Provable.eqv_box (Provable.eqv_symm ha))
          _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
      exact Provable.eqv_trans
        (Provable.eqv_box ha)
        (hboxcof xs n hEval)

/--
It is enough to prove the first-false bridge just for the explicit finite and
cofinite normal-form codes.
-/
theorem box_iter_extensionality_of_explicit_first_false
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys))
    (hcof : ∀ a : LetterlessFormula, ∀ xs : List Nat,
      normalize a = NormalForm.cofinite xs →
      Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs))
    (hfffin : ∀ ys : List Nat, ∀ n : Nat,
      LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) n = false →
      (∀ k, k < n → LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) k = true) →
      Provable.Eqv
        (□(LetterlessFormula.finiteNormalForm ys))
        (LetterlessFormula.iterBoxBottom (n + 1)))
    (hffcof : ∀ xs : List Nat, ∀ n : Nat,
      LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) n = false →
      (∀ k, k < n → LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) k = true) →
      Provable.Eqv
        (□(LetterlessFormula.cofiniteNormalForm xs))
        (LetterlessFormula.iterBoxBottom (n + 1))) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n) := by
  apply box_iter_extensionality_of_explicit_box_codes hfin hcof
  · intro ys n h
    have hex :
        ∃ t, LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) t = false := by
      refine ⟨succAbove ys, ?_⟩
      rw [LetterlessFormula.eval_finiteNormalForm]
      simp [not_mem_succAbove]
    let ff := firstFalseOfExistsFalse
        (LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys)) hex
    have hm :
        Provable.Eqv
          (□(LetterlessFormula.finiteNormalForm ys))
          (LetterlessFormula.iterBoxBottom (ff.idx + 1)) :=
      hfffin ys ff.idx ff.false_at ff.before_true
    have hsound :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (ff.idx + 1)) =
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
      calc
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (ff.idx + 1)) =
          LetterlessFormula.eval (□(LetterlessFormula.finiteNormalForm ys)) :=
            (Provable.eqv_sound hm).symm
        _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
    exact (eval_iterBoxBottom_injective hsound) ▸ hm
  · intro xs n h
    by_cases hxs : xs = []
    · exfalso
      have htop :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
            LetterlessFormula.eval LetterlessFormula.top := by
        calc
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
            LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) := h.symm
          _ = LetterlessFormula.eval LetterlessFormula.top := by
            simpa [hxs] using (Provable.eqv_sound eqv_box_formula_cofinite_nil)
      exact eval_iterBoxBottom_ne_top n htop
    · have hmfalse :
          LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) (minList xs) = false := by
        rw [LetterlessFormula.eval_cofiniteNormalForm]
        simp [minList_mem_of_ne_nil hxs]
      have hmbefore :
          ∀ k, k < minList xs →
            LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) k = true := by
        intro k hk
        rw [LetterlessFormula.eval_cofiniteNormalForm]
        simp [not_mem_of_lt_minList hxs hk]
      have hm :
          Provable.Eqv
            (□(LetterlessFormula.cofiniteNormalForm xs))
            (LetterlessFormula.iterBoxBottom (minList xs + 1)) :=
        hffcof xs (minList xs) hmfalse hmbefore
      have hsound :
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (minList xs + 1)) =
            LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
        calc
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (minList xs + 1)) =
            LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) :=
            (Provable.eqv_sound hm).symm
          _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
      exact (eval_iterBoxBottom_injective hsound) ▸ hm

/--
For a cofinite normal form, having first false time `n` means exactly that `n`
is the least missing index, i.e. the minimum element of the finite hole list.
-/
theorem first_false_cofiniteNormalForm_characterization
    (xs : List Nat) (n : Nat)
    (hnfalse : LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) n = false)
    (hbefore : ∀ k, k < n → LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) k = true) :
    xs ≠ [] ∧ minList xs = n := by
  have hmem : n ∈ xs := by
    rw [LetterlessFormula.eval_cofiniteNormalForm] at hnfalse
    simpa using hnfalse
  have hxs : xs ≠ [] := by
    intro hnil
    simp [hnil] at hmem
  have hminle : minList xs ≤ n := minList_le_of_mem hxs hmem
  have hnlemin : n ≤ minList xs := by
    by_cases hlt : n < minList xs
    · exact Nat.le_of_lt hlt
    · exact Nat.le_of_not_gt (by
        intro hgt
        have htrue : LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) (minList xs) = true :=
          hbefore (minList xs) hgt
        have hfalse : LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) (minList xs) = false := by
          rw [LetterlessFormula.eval_cofiniteNormalForm]
          simp [minList_mem_of_ne_nil hxs]
        simp [hfalse] at htrue)
  exact ⟨hxs, Nat.le_antisymm hminle hnlemin⟩

/--
For a finite normal form, a first false time `n` means precisely that all
indices below `n` are present and `n` itself is missing.
-/
theorem first_false_finiteNormalForm_characterization
    (ys : List Nat) (n : Nat)
    (hnfalse : LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) n = false)
    (hbefore : ∀ k, k < n → LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) k = true) :
    n ∉ ys ∧ ∀ k, k < n → k ∈ ys := by
  constructor
  · intro hmem
    have htrue :
        LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) n = true :=
      (LetterlessFormula.eval_finiteNormalForm_true_iff ys n).2 hmem
    simp [htrue] at hnfalse
  · intro k hk
    have htrue :
        LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) k = true :=
      hbefore k hk
    exact (LetterlessFormula.eval_finiteNormalForm_true_iff ys k).1 htrue

/--
If a finite initial segment has no overlap with the hole list `xs`, then it
implies the corresponding cofinite normal form.
-/
theorem iterBoxBottom_implies_cofiniteNormalForm_of_lt_not_mem
    (xs : List Nat) (n : Nat)
    (hno : ∀ k, k < n → k ∉ xs) :
    Provable
      (LetterlessFormula.iterBoxBottom n ⇒
        LetterlessFormula.cofiniteNormalForm xs) := by
  have himp :
      Provable.Eqv
        (NormalForm.imp (NormalForm.finite (List.range n)) (NormalForm.cofinite xs)).toFormula
        (LetterlessFormula.finiteNormalForm (List.range n) ⇒
          LetterlessFormula.cofiniteNormalForm xs) := by
    simpa using
      (eqv_imp_normalForm
        (NormalForm.finite (List.range n))
        (NormalForm.cofinite xs))
  have htopNF :
      Provable.Eqv
        (NormalForm.imp (NormalForm.finite (List.range n)) (NormalForm.cofinite xs)).toFormula
        LetterlessFormula.top := by
    have hEvalTop :
        LetterlessFormula.eval
            (NormalForm.imp (NormalForm.finite (List.range n)) (NormalForm.cofinite xs)).toFormula =
          LetterlessFormula.eval LetterlessFormula.top := by
      funext t
      have hnot : t ∉ NormalForm.inter (List.range n) xs := by
        intro ht
        rcases (NormalForm.mem_inter_iff (List.range n) xs t).1 ht with ⟨hrange, hxs⟩
        exact hno t (by simpa [List.mem_range] using hrange) hxs
      simp [NormalForm.imp, NormalForm.toFormula, LetterlessFormula.eval_cofiniteNormalForm,
        LetterlessFormula.eval_top, hnot, const1, const]
    exact Provable.eqv_trans
      (eqv_normalForm_of_eval_eq_cofiniteNormalForm
        (NormalForm.imp (NormalForm.finite (List.range n)) (NormalForm.cofinite xs)) [] (by
          simpa [NormalForm.toFormula, LetterlessFormula.cofiniteNormalForm,
            LetterlessFormula.top] using hEvalTop))
      eqv_cofinite_nil_top
  have htopFormula :
      Provable.Eqv
        (LetterlessFormula.finiteNormalForm (List.range n) ⇒
          LetterlessFormula.cofiniteNormalForm xs)
        LetterlessFormula.top :=
    Provable.eqv_trans (Provable.eqv_symm himp) htopNF
  have hprovFinite :
      Provable
        (LetterlessFormula.finiteNormalForm (List.range n) ⇒
          LetterlessFormula.cofiniteNormalForm xs) :=
    Provable.modusPonens htopFormula.2 provable_top
  exact Provable.imp_trans
    (eqv_finite_range_iterBoxBottom n).2
    hprovFinite

/--
Boxing the single-hole cofinite normal form gives the next initial segment.
-/
theorem eqv_box_formula_cofinite_singleton (n : Nat) :
    Provable.Eqv
      (□(LetterlessFormula.cofiniteNormalForm [n]))
      (LetterlessFormula.iterBoxBottom (n + 1)) := by
  have hclause :
      Provable.Eqv
        (LetterlessFormula.cofiniteNormalForm [n])
        (LetterlessFormula.adjacentClause n) :=
    Provable.eqv_symm (Provable.eqv_adjacentClause_singleHole n)
  have hboxClause :
      Provable.Eqv
        (□(LetterlessFormula.adjacentClause n))
        (LetterlessFormula.iterBoxBottom (n + 1)) := by
    constructor
    · exact Provable.axiomLob (LetterlessFormula.iterBoxBottom n)
    · have hinner :
          Provable
            (LetterlessFormula.iterBoxBottom n ⇒
              LetterlessFormula.adjacentClause n) := by
        simpa [LetterlessFormula.adjacentClause, iterClause] using
          (Provable.axiom1
            (LetterlessFormula.iterBoxBottom n)
            (LetterlessFormula.iterBoxBottom (n + 1)))
      have hboxed :
          Provable
            (□(LetterlessFormula.iterBoxBottom n) ⇒
              □(LetterlessFormula.adjacentClause n)) :=
        Provable.box_mono hinner
      exact Provable.imp_trans
        (Provable.eqv_symm (eqv_box_iterBoxBottom n)).1
        hboxed
  exact Provable.eqv_trans
    (Provable.eqv_box hclause)
    hboxClause

/--
If `n` is not in the support list, the corresponding finite normal form implies
the single-hole cofinite normal form at `n`.
-/
theorem finiteNormalForm_implies_cofiniteSingleton_of_not_mem
    (ys : List Nat) (n : Nat) (hnot : n ∉ ys) :
    Provable
      (LetterlessFormula.finiteNormalForm ys ⇒
        LetterlessFormula.cofiniteNormalForm [n]) := by
  have himp :
      Provable.Eqv
        (NormalForm.imp (NormalForm.finite ys) (NormalForm.cofinite [n])).toFormula
        (LetterlessFormula.finiteNormalForm ys ⇒
          LetterlessFormula.cofiniteNormalForm [n]) := by
    simpa using
      (eqv_imp_normalForm
        (NormalForm.finite ys)
        (NormalForm.cofinite [n]))
  have htopNF :
      Provable.Eqv
        (NormalForm.imp (NormalForm.finite ys) (NormalForm.cofinite [n])).toFormula
        LetterlessFormula.top := by
    have hinter :
        NormalForm.inter ys [n] = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro t ht
      rcases (NormalForm.mem_inter_iff ys [n] t).1 ht with ⟨htys, hmem⟩
      simp at hmem
      subst t
      exact hnot htys
    simpa [NormalForm.imp, NormalForm.toFormula, hinter] using
      (eqv_cofinite_nil_top : Provable.Eqv (LetterlessFormula.cofiniteNormalForm []) LetterlessFormula.top)
  have htopFormula :
      Provable.Eqv
        (LetterlessFormula.finiteNormalForm ys ⇒
          LetterlessFormula.cofiniteNormalForm [n])
        LetterlessFormula.top :=
    Provable.eqv_trans (Provable.eqv_symm himp) htopNF
  exact Provable.modusPonens htopFormula.2 provable_top

/--
If `n` is the first missing index of the support list `ys`, then boxing the
finite normal form on `ys` yields `□^(n+1)⊥`.
-/
theorem eqv_box_formula_finite_of_first_false
    (ys : List Nat) (n : Nat)
    (hnot : n ∉ ys)
    (hbefore : ∀ k, k < n → k ∈ ys) :
    Provable.Eqv
      (□(LetterlessFormula.finiteNormalForm ys))
      (LetterlessFormula.iterBoxBottom (n + 1)) := by
  constructor
  · have hmono :
        Provable
          (LetterlessFormula.finiteNormalForm ys ⇒
            LetterlessFormula.cofiniteNormalForm [n]) :=
      finiteNormalForm_implies_cofiniteSingleton_of_not_mem ys n hnot
    exact Provable.imp_trans
      (Provable.box_mono hmono)
      (eqv_box_formula_cofinite_singleton n).1
  · have hrange :
        ∀ t : Nat, t ∈ List.range n → t ∈ ys := by
      intro t ht
      exact hbefore t (by simpa [List.mem_range] using ht)
    have hmono :
        Provable
          (LetterlessFormula.finiteNormalForm (List.range n) ⇒
            LetterlessFormula.finiteNormalForm ys) :=
      provable_finiteNormalForm_mono hrange
    exact Provable.imp_trans
      (eqv_box_formula_finite_range n).2
      (Provable.box_mono hmono)

/--
Boxed initial-segment extensionality for the explicit finite normal-form
codes.
-/
theorem box_iter_extensionality_explicit_finite
    (ys : List Nat) (n : Nat)
    (h :
      LetterlessFormula.eval (□(LetterlessFormula.finiteNormalForm ys)) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv
      (□(LetterlessFormula.finiteNormalForm ys))
      (LetterlessFormula.iterBoxBottom n) := by
  cases n with
  | zero =>
      exact False.elim (eval_box_ne_iterBoxBottom_zero _ h)
  | succ m =>
      rcases first_false_of_eval_box_eq_iterBoxBottom_succ
          (LetterlessFormula.finiteNormalForm ys) m h with
        ⟨hmfalse, hmbefore⟩
      rcases first_false_finiteNormalForm_characterization ys m hmfalse hmbefore with
        ⟨hnot, hbefore⟩
      simpa using eqv_box_formula_finite_of_first_false ys m hnot hbefore

/--
Boxing a nonempty cofinite normal form yields the initial segment determined
by its least hole.
-/
theorem eqv_box_formula_cofinite_nonempty (xs : List Nat) (hxs : xs ≠ []) :
    Provable.Eqv
      (□(LetterlessFormula.cofiniteNormalForm xs))
      (LetterlessFormula.iterBoxBottom (minList xs + 1)) := by
  constructor
  · have hmono :
        Provable
          (LetterlessFormula.cofiniteNormalForm xs ⇒
            LetterlessFormula.cofiniteNormalForm [minList xs]) :=
      provable_cofiniteNormalForm_antimono (fun t ht => by
        simp at ht
        subst t
        exact minList_mem_of_ne_nil hxs)
    exact Provable.imp_trans
      (Provable.box_mono hmono)
      (eqv_box_formula_cofinite_singleton (minList xs)).1
  · have hiterCof :
        Provable
          (LetterlessFormula.iterBoxBottom (minList xs) ⇒
            LetterlessFormula.cofiniteNormalForm xs) :=
      iterBoxBottom_implies_cofiniteNormalForm_of_lt_not_mem xs (minList xs)
        (fun k hk => not_mem_of_lt_minList hxs hk)
    exact Provable.imp_trans
      (Provable.eqv_symm (eqv_box_iterBoxBottom (minList xs))).1
      (Provable.box_mono hiterCof)

/--
Boxed initial-segment extensionality for the explicit cofinite normal-form
codes.
-/
theorem box_iter_extensionality_explicit_cofinite
    (xs : List Nat) (n : Nat)
    (h :
      LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n)) :
    Provable.Eqv
      (□(LetterlessFormula.cofiniteNormalForm xs))
      (LetterlessFormula.iterBoxBottom n) := by
  by_cases hxs : xs = []
  · exfalso
    have htop :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
          LetterlessFormula.eval LetterlessFormula.top := by
      calc
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
          LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) := h.symm
        _ = LetterlessFormula.eval LetterlessFormula.top := by
          simpa [hxs] using (Provable.eqv_sound eqv_box_formula_cofinite_nil)
    exact eval_iterBoxBottom_ne_top n htop
  · have hm :
        Provable.Eqv
          (□(LetterlessFormula.cofiniteNormalForm xs))
          (LetterlessFormula.iterBoxBottom (minList xs + 1)) :=
      eqv_box_formula_cofinite_nonempty xs hxs
    have hsound :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (minList xs + 1)) =
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
      calc
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (minList xs + 1)) =
          LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) :=
            (Provable.eqv_sound hm).symm
        _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
    exact (eval_iterBoxBottom_injective hsound) ▸ hm

/--
Once boxed extensionality is known for the explicit finite codes, the explicit
cofinite codes follow automatically from the empty and nonempty cofinite
computations.
-/
theorem box_iter_extensionality_of_explicit_finite_only
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys))
    (hboxfin : ∀ ys : List Nat, ∀ n : Nat,
      LetterlessFormula.eval (□(LetterlessFormula.finiteNormalForm ys)) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv
        (□(LetterlessFormula.finiteNormalForm ys))
        (LetterlessFormula.iterBoxBottom n)) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n) := by
  apply box_iter_extensionality_of_explicit_box_codes
    hfin
    (cofinite_shape_normalization_of_finite hfin)
    hboxfin
  intro xs n h
  by_cases hxs : xs = []
  · exfalso
    have htop :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
          LetterlessFormula.eval LetterlessFormula.top := by
      calc
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) =
          LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) := h.symm
        _ = LetterlessFormula.eval LetterlessFormula.top := by
          simpa [hxs] using (Provable.eqv_sound eqv_box_formula_cofinite_nil)
    exact eval_iterBoxBottom_ne_top n htop
  · have hm :
        Provable.Eqv
          (□(LetterlessFormula.cofiniteNormalForm xs))
          (LetterlessFormula.iterBoxBottom (minList xs + 1)) :=
      eqv_box_formula_cofinite_nonempty xs hxs
    have hsound :
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (minList xs + 1)) =
          LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := by
      calc
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom (minList xs + 1)) =
          LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm xs)) :=
            (Provable.eqv_sound hm).symm
        _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) := h
    exact (eval_iterBoxBottom_injective hsound) ▸ hm

/--
So finite-shape normalization for arbitrary formulas already implies boxed
initial-segment extensionality.
-/
theorem box_iter_extensionality_of_finite_shape_normalization
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys)) :
    ∀ a : LetterlessFormula, ∀ n : Nat,
      LetterlessFormula.eval (□a) =
        LetterlessFormula.eval (LetterlessFormula.iterBoxBottom n) →
      Provable.Eqv (□a) (LetterlessFormula.iterBoxBottom n) :=
  box_iter_extensionality_of_explicit_finite_only
    hfin
    box_iter_extensionality_explicit_finite

/--
Equivalently, finite-shape normalization alone suffices for full recursive
normalization/completeness.
-/
theorem normalization_of_finite_shape_normalization
    (hfin : ∀ a : LetterlessFormula, ∀ ys : List Nat,
      normalize a = NormalForm.finite ys →
      Provable.Eqv a (LetterlessFormula.finiteNormalForm ys)) :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a :=
  normalization_iff_box_iter_extensionality.mpr
    (box_iter_extensionality_of_finite_shape_normalization hfin)

/--
Direct explicit finite/cofinite shape normalization by structural induction.
-/
theorem explicit_shape_normalization
    : ∀ a : LetterlessFormula,
      (∀ ys : List Nat,
        normalize a = NormalForm.finite ys →
        Provable.Eqv a (LetterlessFormula.finiteNormalForm ys)) ∧
      (∀ xs : List Nat,
        normalize a = NormalForm.cofinite xs →
        Provable.Eqv a (LetterlessFormula.cofiniteNormalForm xs)) := by
  intro a
  induction a with
  | bottom =>
      constructor
      · intro ys hys
        have hnil : ys = [] := by
          simpa [normalize] using hys
        simpa [hnil, LetterlessFormula.finiteNormalForm] using
          (Provable.eqv_refl (⊥ : LetterlessFormula))
      · intro xs hxs
        cases hxs
  | imp a b iha ihb =>
      rcases iha with ⟨ihafin, ihacof⟩
      rcases ihb with ⟨ihbfin, ihbcof⟩
      constructor
      · intro ys hys
        cases hna : normalize a with
        | finite as =>
            cases hnb : normalize b with
            | finite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hys
            | cofinite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hys
        | cofinite as =>
            cases hnb : normalize b with
            | cofinite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hys
            | finite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.cofiniteNormalForm as) :=
                  ihacof as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.finiteNormalForm bs) :=
                  ihbfin bs hnb
                have hlist : ys = as ++ bs := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hys.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.cofinite as) (NormalForm.finite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.cofinite as) (NormalForm.finite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
      · intro xs hxs
        cases hna : normalize a with
        | finite as =>
            cases hnb : normalize b with
            | finite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.finiteNormalForm as) :=
                  ihafin as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.finiteNormalForm bs) :=
                  ihbfin bs hnb
                have hlist : xs = NormalForm.diff as bs := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hxs.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.finite as) (NormalForm.finite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.finite as) (NormalForm.finite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
            | cofinite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.finiteNormalForm as) :=
                  ihafin as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.cofiniteNormalForm bs) :=
                  ihbcof bs hnb
                have hlist : xs = NormalForm.inter as bs := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hxs.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.finite as) (NormalForm.cofinite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.finite as) (NormalForm.cofinite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
        | cofinite as =>
            cases hnb : normalize b with
            | finite bs =>
                simp [normalize, hna, hnb, NormalForm.imp] at hxs
            | cofinite bs =>
                have ha :
                    Provable.Eqv a (LetterlessFormula.cofiniteNormalForm as) :=
                  ihacof as hna
                have hb :
                    Provable.Eqv b (LetterlessFormula.cofiniteNormalForm bs) :=
                  ihbcof bs hnb
                have hlist : xs = NormalForm.diff bs as := by
                  simpa [normalize, hna, hnb, NormalForm.imp] using hxs.symm
                have himp :
                    Provable.Eqv (a ⇒ b)
                      ((NormalForm.imp (NormalForm.cofinite as) (NormalForm.cofinite bs)).toFormula) := by
                  exact Provable.eqv_trans
                    (Provable.eqv_imp ha hb)
                    (Provable.eqv_symm
                      (eqv_imp_normalForm (NormalForm.cofinite as) (NormalForm.cofinite bs)))
                simpa [hlist, NormalForm.imp, NormalForm.toFormula] using himp
  | box a iha =>
      rcases iha with ⟨ihafin, ihacof⟩
      constructor
      · intro ys hys
        have hEvalFinite :
            LetterlessFormula.eval (□a) =
              LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) := by
          calc
            LetterlessFormula.eval (□a) = LetterlessFormula.eval (normalize (□a)).toFormula :=
              (eval_normalize (□a)).symm
            _ = LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) := by
              simp [hys, NormalForm.toFormula]
        rcases box_all_true_or_exists_firstFalse (LetterlessFormula.eval a) with hconst | ⟨ff, -⟩
        · exfalso
          have htop :
              LetterlessFormula.eval (□a) =
                LetterlessFormula.eval LetterlessFormula.top := by
            simpa [LetterlessFormula.eval_box, LetterlessFormula.eval_top] using hconst
          exact eval_finiteNormalForm_ne_top ys (Eq.trans hEvalFinite.symm htop)
        · have hiter :
              LetterlessFormula.eval (□a) =
                LetterlessFormula.eval (LetterlessFormula.iterBoxBottom ff.idx) := by
            simpa [LetterlessFormula.eval_box] using
              (eval_box_eq_iterBoxBottom_of_box_first_false
                (LetterlessFormula.eval a) ff.idx ff.false_at ff.before_true)
          have hysIter :
              LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
                LetterlessFormula.eval (LetterlessFormula.iterBoxBottom ff.idx) := by
            exact Eq.trans hEvalFinite.symm hiter
          cases hna : normalize a with
          | finite zs =>
              have ha :
                  Provable.Eqv a (LetterlessFormula.finiteNormalForm zs) :=
                ihafin zs hna
              have hzIter :
                  LetterlessFormula.eval (□(LetterlessFormula.finiteNormalForm zs)) =
                    LetterlessFormula.eval (LetterlessFormula.iterBoxBottom ff.idx) := by
                calc
                  LetterlessFormula.eval (□(LetterlessFormula.finiteNormalForm zs)) =
                    LetterlessFormula.eval (□a) := by
                      exact Provable.eqv_sound (Provable.eqv_box (Provable.eqv_symm ha))
                  _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom ff.idx) := hiter
              exact Provable.eqv_trans
                (Provable.eqv_trans (Provable.eqv_box ha)
                  (box_iter_extensionality_explicit_finite zs ff.idx hzIter))
                (Provable.eqv_symm
                  (eqv_finiteNormalForm_of_eval_eq_iterBoxBottom ys ff.idx hysIter))
          | cofinite zs =>
              have ha :
                  Provable.Eqv a (LetterlessFormula.cofiniteNormalForm zs) :=
                ihacof zs hna
              have hzIter :
                  LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm zs)) =
                    LetterlessFormula.eval (LetterlessFormula.iterBoxBottom ff.idx) := by
                calc
                  LetterlessFormula.eval (□(LetterlessFormula.cofiniteNormalForm zs)) =
                    LetterlessFormula.eval (□a) := by
                      exact Provable.eqv_sound (Provable.eqv_box (Provable.eqv_symm ha))
                  _ = LetterlessFormula.eval (LetterlessFormula.iterBoxBottom ff.idx) := hiter
              exact Provable.eqv_trans
                (Provable.eqv_trans (Provable.eqv_box ha)
                  (box_iter_extensionality_explicit_cofinite zs ff.idx hzIter))
                (Provable.eqv_symm
                  (eqv_finiteNormalForm_of_eval_eq_iterBoxBottom ys ff.idx hysIter))
      · intro xs hxs
        exact box_cofinite_shape_of_subformula_shapes a ihacof xs hxs

/--
Full recursive normalization for the letterless fragment.
-/
theorem normalization :
    ∀ a : LetterlessFormula, Provable.Eqv (normalize a).toFormula a := by
  intro a
  cases hna : normalize a with
  | finite ys =>
      exact Provable.eqv_symm (by
        simpa [hna, NormalForm.toFormula] using (explicit_shape_normalization a).1 ys hna)
  | cofinite xs =>
      exact Provable.eqv_symm (by
        simpa [hna, NormalForm.toFormula] using (explicit_shape_normalization a).2 xs hna)

/--
Completeness for the letterless fragment: if a formula denotes the constantly
true bitstream, then it is provable.
-/
theorem completeness (a : LetterlessFormula)
    (h : LetterlessFormula.eval a = const1) :
    Provable a := by
  have hnorm :
      Provable.Eqv a (normalize a).toFormula :=
    Provable.eqv_symm (normalization a)
  cases hna : normalize a with
  | finite ys =>
      exfalso
      have htop :
          LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
            LetterlessFormula.eval LetterlessFormula.top := by
        calc
          LetterlessFormula.eval (LetterlessFormula.finiteNormalForm ys) =
            LetterlessFormula.eval (normalize a).toFormula := by
              simp [hna, NormalForm.toFormula]
          _ = LetterlessFormula.eval a := eval_normalize a
          _ = LetterlessFormula.eval LetterlessFormula.top := by
              simpa [LetterlessFormula.eval_top] using h
      exact eval_finiteNormalForm_ne_top ys htop
  | cofinite xs =>
      have htop :
          LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) =
            LetterlessFormula.eval LetterlessFormula.top := by
        calc
          LetterlessFormula.eval (LetterlessFormula.cofiniteNormalForm xs) =
            LetterlessFormula.eval (normalize a).toFormula := by
              simp [hna, NormalForm.toFormula]
          _ = LetterlessFormula.eval a := eval_normalize a
          _ = LetterlessFormula.eval LetterlessFormula.top := by
              simpa [LetterlessFormula.eval_top] using h
      have hcof :
          Provable.Eqv (LetterlessFormula.cofiniteNormalForm xs) LetterlessFormula.top :=
        eqv_cofiniteNormalForm_of_eval_eq_top xs htop
      have hnormTop :
          Provable.Eqv (normalize a).toFormula LetterlessFormula.top := by
        simpa [hna, NormalForm.toFormula] using hcof
      have haTop : Provable.Eqv a LetterlessFormula.top :=
        Provable.eqv_trans (Provable.eqv_symm (normalization a)) hnormTop
      exact Provable.modusPonens haTop.2 provable_top

/--
Soundness and completeness for the letterless fragment.
-/
theorem provable_iff_eval_const1 (a : LetterlessFormula) :
    Provable a ↔ LetterlessFormula.eval a = const1 := by
  constructor
  · exact provable_sound
  · exact completeness a

end Bitstream
