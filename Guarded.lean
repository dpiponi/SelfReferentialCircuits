import Bitstream.FixedPoints
import Bitstream.Letterless

namespace Bitstream

inductive OneLetterFormula where
  | bottom : OneLetterFormula
  | var : OneLetterFormula
  | imp : OneLetterFormula → OneLetterFormula → OneLetterFormula
  | box : OneLetterFormula → OneLetterFormula
deriving DecidableEq, Repr

namespace OneLetterFormula

def neg (φ : OneLetterFormula) : OneLetterFormula := imp φ bottom

def top : OneLetterFormula := imp bottom bottom

def ofLetterless : _root_.Bitstream.LetterlessFormula → OneLetterFormula
  | _root_.Bitstream.LetterlessFormula.bottom => bottom
  | _root_.Bitstream.LetterlessFormula.imp φ ψ => imp (ofLetterless φ) (ofLetterless ψ)
  | _root_.Bitstream.LetterlessFormula.box φ => box (ofLetterless φ)

def substitute (σ : OneLetterFormula) : OneLetterFormula → OneLetterFormula
  | bottom => bottom
  | var => σ
  | imp φ ψ => imp (substitute σ φ) (substitute σ ψ)
  | box φ => box (substitute σ φ)

def eval (p : Bitstream) : OneLetterFormula → Bitstream
  | bottom => const0
  | var => p
  | imp φ ψ => eval p φ =⇒ eval p ψ
  | box φ => Bitstream.box (eval p φ)

def modalizedAux (underBox : Bool) : OneLetterFormula → Bool
  | bottom => true
  | var => underBox
  | imp φ ψ => modalizedAux underBox φ && modalizedAux underBox ψ
  | box φ => modalizedAux true φ

def modalized (φ : OneLetterFormula) : Bool := modalizedAux false φ

def guarded (φ : OneLetterFormula) : Prop := modalized φ = true

theorem guarded_bottom : guarded bottom := rfl

theorem guarded_top : guarded top := rfl

theorem modalizedAux_ofLetterless (underBox : Bool) (φ : _root_.Bitstream.LetterlessFormula) :
    modalizedAux underBox (ofLetterless φ) = true := by
  induction φ generalizing underBox with
  | bottom =>
      rfl
  | imp φ ψ ihφ ihψ =>
      simp [ofLetterless, modalizedAux, ihφ, ihψ]
  | box φ ih =>
      simp [ofLetterless, modalizedAux, ih]

theorem guarded_ofLetterless (φ : _root_.Bitstream.LetterlessFormula) :
    guarded (ofLetterless φ) := by
  simpa [guarded, modalized] using modalizedAux_ofLetterless false φ

theorem box_eq_of_agree_prefix {s u : Bitstream} {t : Time}
    (hag : ∀ k, k < t → s k = u k) :
    Bitstream.box s t = Bitstream.box u t := by
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      have hhead : s t = u t := hag t (Nat.lt_succ_self t)
      have htail : Bitstream.box s t = Bitstream.box u t := ih (fun k hk => hag k (Nat.lt_trans hk (Nat.lt_succ_self t)))
      simp [Bitstream.box, htail, hhead]

theorem eval_eq_of_agree_prefix_aux
    (φ : OneLetterFormula)
    {underBox : Bool}
    (hguard : modalizedAux underBox φ = true)
    {p q : Bitstream}
    {t : Time}
    (hag : ∀ k, k < t + cond underBox 1 0 → p k = q k) :
    eval p φ t = eval q φ t := by
  induction φ generalizing underBox t with
  | bottom =>
      rfl
  | var =>
      cases underBox with
      | false =>
          simp [modalizedAux] at hguard
      | true =>
          have hpq : p t = q t := hag t (by simp)
          simpa [eval] using hpq
  | imp φ ψ ihφ ihψ =>
      have hboth := hguard
      simp [modalizedAux] at hboth
      rcases hboth with ⟨hφ, hψ⟩
      have hEqφ : eval p φ t = eval q φ t := ihφ hφ hag
      have hEqψ : eval p ψ t = eval q ψ t := ihψ hψ hag
      simp [eval, bimplies, hEqφ, hEqψ]
  | box φ ih =>
      have hφ : modalizedAux true φ = true := by
        simpa [modalizedAux] using hguard
      have hprefix :
          ∀ k, k < t → eval p φ k = eval q φ k := by
        intro k hk
        apply ih hφ
        intro j hj
        have hj' : j < k + 1 := by simpa using hj
        have hkt : k + 1 ≤ t := Nat.succ_le_of_lt hk
        have hjt : j < t := Nat.lt_of_lt_of_le hj' hkt
        exact hag j (Nat.lt_of_lt_of_le hjt (Nat.le_add_right t (cond underBox 1 0)))
      exact box_eq_of_agree_prefix hprefix

theorem eval_substitute (φ σ : OneLetterFormula) (p : Bitstream) :
    eval p (substitute σ φ) = eval (eval p σ) φ := by
  induction φ with
  | bottom =>
      rfl
  | var =>
      rfl
  | imp φ ψ ihφ ihψ =>
      simp [substitute, eval, ihφ, ihψ]
  | box φ ih =>
      simp [substitute, eval, ih]

theorem eval_ofLetterless (φ : _root_.Bitstream.LetterlessFormula) (p : Bitstream) :
    eval p (ofLetterless φ) = _root_.Bitstream.LetterlessFormula.eval φ := by
  induction φ with
  | bottom =>
      rfl
  | imp φ ψ ihφ ihψ =>
      simp [ofLetterless, eval, _root_.Bitstream.LetterlessFormula.eval, ihφ, ihψ]
  | box φ ih =>
      simp [ofLetterless, eval, _root_.Bitstream.LetterlessFormula.eval, ih]

theorem eval_lob
    (p : Bitstream)
    (φ : OneLetterFormula)
    (h : eval p (OneLetterFormula.imp (OneLetterFormula.box φ) φ) = const1) :
    eval p φ = const1 := by
  simpa [eval] using lob_true (eval p φ) h

theorem eval_eventuallyConstant
    (φ : OneLetterFormula)
    (hguard : guarded φ)
    (p : Bitstream) :
    EventuallyConstant (eval p φ) := by
  induction φ with
  | bottom =>
      exact ⟨0, false, by intro t _; rfl⟩
  | var =>
      simp [guarded, modalized, modalizedAux] at hguard
  | imp φ ψ ihφ ihψ =>
      have hboth := hguard
      simp [guarded, modalized, modalizedAux] at hboth
      rcases hboth with ⟨hφ, hψ⟩
      rcases ihφ hφ with ⟨Nφ, bφ, hφc⟩
      rcases ihψ hψ with ⟨Nψ, bψ, hψc⟩
      refine ⟨max Nφ Nψ, (!bφ) || bψ, ?_⟩
      intro t ht
      have htφ : Nφ ≤ t := Nat.le_trans (Nat.le_max_left _ _) ht
      have htψ : Nψ ≤ t := Nat.le_trans (Nat.le_max_right _ _) ht
      simp [eval, bimplies, hφc t htφ, hψc t htψ]
  | box φ ih =>
      simpa [eval] using box_eventuallyConstant (eval p φ)

end OneLetterFormula

abbrev GuardedFormula : Type := { φ : OneLetterFormula // OneLetterFormula.guarded φ }

namespace GuardedFormula

def formula (φ : GuardedFormula) : OneLetterFormula := φ.1

theorem eval_eq_of_agree_prefix
    (φ : GuardedFormula)
    {p q : Bitstream}
    {t : Time}
    (hag : ∀ k, k < t → p k = q k) :
    OneLetterFormula.eval p (formula φ) t = OneLetterFormula.eval q (formula φ) t := by
  apply OneLetterFormula.eval_eq_of_agree_prefix_aux (underBox := false) (formula φ) φ.2
  intro k hk
  exact hag k (by simpa using hk)

def eval (φ : GuardedFormula) : Bitstream → Bitstream := fun p => OneLetterFormula.eval p φ.1

def selfSubstitute (φ : GuardedFormula) : OneLetterFormula :=
  OneLetterFormula.substitute φ.1 φ.1

theorem eval_selfSubstitute (φ : GuardedFormula) (p : Bitstream) :
    OneLetterFormula.eval p (selfSubstitute φ) = eval φ (eval φ p) := by
  simpa [selfSubstitute, eval] using OneLetterFormula.eval_substitute φ.1 φ.1 p

def IsRealizedBy (φ : GuardedFormula) (q : _root_.Bitstream.LetterlessFormula) : Prop :=
  eval φ (_root_.Bitstream.LetterlessFormula.eval q) = _root_.Bitstream.LetterlessFormula.eval q

def HasSemanticFixedPoint (φ : GuardedFormula) : Prop :=
  ∃ s : Bitstream, eval φ s = s

def HasLetterlessFixedPoint (φ : GuardedFormula) : Prop :=
  ∃ q : _root_.Bitstream.LetterlessFormula, IsRealizedBy φ q

def solveBit (φ : GuardedFormula) : Nat → Bit := fun
  | 0 => OneLetterFormula.eval const0 (formula φ) 0
  | t + 1 =>
      OneLetterFormula.eval
        (fun k => if _h : k < t + 1 then solveBit φ k else false)
        (formula φ)
        (t + 1)

def solve (φ : GuardedFormula) : Bitstream := solveBit φ

def boxVar : GuardedFormula :=
  ⟨OneLetterFormula.box OneLetterFormula.var, rfl⟩

def boxNotVar : GuardedFormula :=
  ⟨OneLetterFormula.box (OneLetterFormula.neg OneLetterFormula.var), rfl⟩

theorem eval_boxVar (p : Bitstream) : eval boxVar p = box p := rfl

theorem solve_is_fixedPoint (φ : GuardedFormula) : eval φ (solve φ) = solve φ := by
  funext t
  cases t with
  | zero =>
      have hsame :
          OneLetterFormula.eval (solve φ) (formula φ) 0 =
            OneLetterFormula.eval const0 (formula φ) 0 := by
        apply eval_eq_of_agree_prefix φ
        intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
      simpa [solve, solveBit] using hsame
  | succ t =>
      have hsame :
          OneLetterFormula.eval (solve φ) (formula φ) (t + 1) =
          OneLetterFormula.eval
              (fun k => if _h : k < t + 1 then solveBit φ k else false)
              (formula φ)
              (t + 1) := by
        apply eval_eq_of_agree_prefix φ
        intro k hk
        simp [solve, hk]
      simpa [solve, solveBit] using hsame

theorem eval_boxNotVar (p : Bitstream) : eval boxNotVar p = box (∼p) := by
  have hneg : OneLetterFormula.eval p (OneLetterFormula.neg OneLetterFormula.var) = ∼p := by
    funext t
    cases hp : p t <;> simp [OneLetterFormula.eval, OneLetterFormula.neg, bimplies, const0, const, bnot, hp]
  simp [eval, boxNotVar, OneLetterFormula.eval, hneg]

theorem boxVar_realized_by_top : IsRealizedBy boxVar _root_.Bitstream.LetterlessFormula.top := by
  simpa [IsRealizedBy, eval_boxVar] using box_const1

theorem boxNotVar_realized_by_boxBottom :
    IsRealizedBy boxNotVar (_root_.Bitstream.LetterlessFormula.box _root_.Bitstream.LetterlessFormula.bottom) := by
  have hq :
      _root_.Bitstream.LetterlessFormula.eval
        (_root_.Bitstream.LetterlessFormula.box _root_.Bitstream.LetterlessFormula.bottom) = pulse := by
    funext t
    cases t with
    | zero =>
        rfl
    | succ t =>
        cases t with
        | zero =>
            simp [_root_.Bitstream.LetterlessFormula.eval, box, const0, const, pulse]
        | succ t =>
            simp [_root_.Bitstream.LetterlessFormula.eval, box, const0, const, pulse]
  simpa [IsRealizedBy, eval_boxNotVar, hq] using pulse_eq_box_not_pulse.symm

theorem realizedBy_gives_semanticFixedPoint
    {φ : GuardedFormula}
    {q : _root_.Bitstream.LetterlessFormula}
    (h : IsRealizedBy φ q) :
    HasSemanticFixedPoint φ := by
  refine ⟨_root_.Bitstream.LetterlessFormula.eval q, ?_⟩
  exact h

theorem boxVar_hasLetterlessFixedPoint : HasLetterlessFixedPoint boxVar := by
  exact ⟨_root_.Bitstream.LetterlessFormula.top, boxVar_realized_by_top⟩

theorem boxNotVar_hasLetterlessFixedPoint : HasLetterlessFixedPoint boxNotVar := by
  exact ⟨_root_.Bitstream.LetterlessFormula.box _root_.Bitstream.LetterlessFormula.bottom,
    boxNotVar_realized_by_boxBottom⟩

theorem boxVar_hasSemanticFixedPoint : HasSemanticFixedPoint boxVar :=
  realizedBy_gives_semanticFixedPoint boxVar_realized_by_top

theorem boxNotVar_hasSemanticFixedPoint : HasSemanticFixedPoint boxNotVar :=
  realizedBy_gives_semanticFixedPoint boxNotVar_realized_by_boxBottom

theorem solve_hasSemanticFixedPoint (φ : GuardedFormula) : HasSemanticFixedPoint φ := by
  exact ⟨solve φ, solve_is_fixedPoint φ⟩

theorem fixedPoint_unique
    (φ : GuardedFormula)
    {s t : Bitstream}
    (hs : eval φ s = s)
    (ht : eval φ t = t) :
    s = t := by
  have hprefix :
      ∀ u, ∀ k, k < u → s k = t k := by
    intro u
    induction u with
    | zero =>
        intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
    | succ u ihu =>
        intro k hk
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
        | inl hlt =>
            exact ihu k hlt
        | inr heq =>
            have heval : eval φ s u = eval φ t u := eval_eq_of_agree_prefix φ ihu
            have hs' : eval φ s u = s u := congrArg (fun f => f u) hs
            have ht' : eval φ t u = t u := congrArg (fun f => f u) ht
            exact heq ▸ hs'.symm.trans (heval.trans ht')
  funext u
  exact hprefix (u + 1) u (Nat.lt_succ_self u)

theorem solve_is_unique_fixedPoint
    (φ : GuardedFormula)
    {s : Bitstream}
    (hs : eval φ s = s) :
    s = solve φ := by
  exact fixedPoint_unique φ hs (solve_is_fixedPoint φ)

theorem solve_boxVar : solve boxVar = const1 := by
  apply (fixedPoint_box_unique (solve boxVar)).1
  simpa [eval_boxVar] using (solve_is_fixedPoint boxVar).symm

theorem solve_boxNotVar : solve boxNotVar = pulse := by
  apply (fixedPoint_box_not_unique (solve boxNotVar)).1
  simpa [eval_boxNotVar] using (solve_is_fixedPoint boxNotVar).symm

theorem eval_eventuallyConstant (φ : GuardedFormula) (p : Bitstream) :
    EventuallyConstant (eval φ p) :=
  OneLetterFormula.eval_eventuallyConstant φ.1 φ.2 p

theorem solve_eventuallyConstant (φ : GuardedFormula) : EventuallyConstant (solve φ) := by
  have hfixed : solve φ = eval φ (solve φ) := (solve_is_fixedPoint φ).symm
  rw [hfixed]
  exact eval_eventuallyConstant φ (solve φ)

theorem hasLetterlessFixedPoint (φ : GuardedFormula) : HasLetterlessFixedPoint φ := by
  rcases solve_eventuallyConstant φ with ⟨N, b, hstab⟩
  refine ⟨_root_.Bitstream.LetterlessFormula.encodeEventuallyConstant N (solve φ) b, ?_⟩
  have hq :
      _root_.Bitstream.LetterlessFormula.eval
        (_root_.Bitstream.LetterlessFormula.encodeEventuallyConstant N (solve φ) b) =
      solve φ := by
    funext t
    by_cases hlt : t < N
    · simp [_root_.Bitstream.LetterlessFormula.eval_encodeEventuallyConstant, hlt]
    · have hge : N ≤ t := Nat.le_of_not_gt hlt
      simp [_root_.Bitstream.LetterlessFormula.eval_encodeEventuallyConstant, hlt, hstab t hge]
  simpa [IsRealizedBy, hq] using solve_is_fixedPoint φ

theorem hasSemanticFixedPoint_viaLetterless (φ : GuardedFormula) : HasSemanticFixedPoint φ :=
  realizedBy_gives_semanticFixedPoint (hasLetterlessFixedPoint φ).choose_spec

end GuardedFormula

end Bitstream
