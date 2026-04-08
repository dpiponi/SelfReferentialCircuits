import Bitstream.Modal

namespace Bitstream

inductive LetterlessFormula where
  | bottom : LetterlessFormula
  | imp : LetterlessFormula → LetterlessFormula → LetterlessFormula
  | box : LetterlessFormula → LetterlessFormula
deriving DecidableEq, Repr

namespace LetterlessFormula

notation "⊥" => bottom
infixr:60 " ⇒ " => imp
prefix:max "□" => box

def eval : LetterlessFormula → Bitstream
  | ⊥ => const0
  | a ⇒ b => eval a =⇒ eval b
  | LetterlessFormula.box a => Bitstream.box (eval a)

def neg (a : LetterlessFormula) : LetterlessFormula := a ⇒ ⊥
def disj (a b : LetterlessFormula) : LetterlessFormula := neg a ⇒ b

def top : LetterlessFormula := ⊥ ⇒ ⊥
prefix:max "⊤" => top

def iterBoxBottom : Nat → LetterlessFormula
  | 0 => ⊥
  | n + 1 => □(iterBoxBottom n)

def pulseAt (n : Nat) : LetterlessFormula := (□(iterBoxBottom n) ⇒ iterBoxBottom n) ⇒ ⊥
def tailFrom (n : Nat) : LetterlessFormula := neg (iterBoxBottom n)

def encodePrefix (N : Nat) (s : Bitstream) (b : Bit) : Nat → LetterlessFormula
  | 0 => if b then tailFrom N else ⊥
  | n + 1 =>
      let q := encodePrefix N s b n
      if s n then disj (pulseAt n) q else q

def encodeEventuallyConstant (N : Nat) (s : Bitstream) (b : Bit) : LetterlessFormula :=
  encodePrefix N s b N

theorem eval_bottom : eval ⊥ = const0 := rfl

theorem eval_imp (a b : LetterlessFormula) : eval (a ⇒ b) = (eval a =⇒ eval b) := rfl

theorem eval_box (a : LetterlessFormula) : eval (□a) = Bitstream.box (eval a) := rfl

theorem eval_neg (a : LetterlessFormula) : eval (neg a) = ∼(eval a) := by
  funext t
  cases ha : eval a t <;> simp [neg, eval, bimplies, bnot, const0, const, ha]

theorem eval_disj (a b : LetterlessFormula) : eval (disj a b) = eval a ||| eval b := by
  funext t
  cases ha : eval a t <;> cases hb : eval b t <;>
    simp [disj, neg, eval, bimplies, bor, const0, const, ha, hb]

theorem eval_top : eval top = const1 := by
  funext t
  simp [top, eval, bimplies, const0, const1, const]

theorem eval_box_top : eval (LetterlessFormula.box top) = const1 := by
  simpa [eval_top] using box_const1

theorem eval_box_implication_distributes (a b : LetterlessFormula) :
    eval (LetterlessFormula.imp (LetterlessFormula.box (a ⇒ b))
      (LetterlessFormula.imp (LetterlessFormula.box a) (LetterlessFormula.box b))) = const1 := by
  simpa [eval] using box_implication_distributes_true (eval a) (eval b)

theorem eval_box_idempotent_implication (a : LetterlessFormula) :
    eval (LetterlessFormula.imp (LetterlessFormula.box a) (LetterlessFormula.box (LetterlessFormula.box a))) = const1 := by
  simpa [eval] using box_idempotent_implication_true (eval a)

theorem eval_lob (a : LetterlessFormula)
    (h : eval (LetterlessFormula.imp (LetterlessFormula.box a) a) = const1) :
    eval a = const1 := by
  simpa [eval] using lob_true (eval a) h

theorem eval_iterBoxBottom_true_iff (n t : Nat) :
    eval (iterBoxBottom n) t = true ↔ t < n := by
  induction n generalizing t with
  | zero =>
      simp [iterBoxBottom, eval, const0, const]
  | succ n ih =>
      rw [iterBoxBottom, eval_box]
      rw [box_eq_true_iff_prefix_all_true]
      constructor
      · intro h
        cases t with
        | zero =>
            simp
        | succ t =>
            have htn : t < n := (ih t).mp (h t (Nat.lt_succ_self t))
            simpa using Nat.succ_lt_succ htn
      · intro h
        intro k hk
        exact (ih k).mpr (Nat.lt_of_lt_of_le hk (Nat.le_of_lt_succ h))

theorem eval_iterBoxBottom (n : Nat) : eval (iterBoxBottom n) = fun t => decide (t < n) := by
  funext t
  by_cases hlt : t < n
  · have htrue : eval (iterBoxBottom n) t = true := (eval_iterBoxBottom_true_iff n t).mpr hlt
    simp [htrue, hlt]
  · have hfalse : eval (iterBoxBottom n) t = false := by
      cases hval : eval (iterBoxBottom n) t with
      | false => exact rfl
      | true =>
          exact False.elim (hlt ((eval_iterBoxBottom_true_iff n t).mp hval))
    simp [hfalse, hlt]

theorem eval_pulseAt_true_iff (n t : Nat) :
    eval (pulseAt n) t = true ↔ t = n := by
  constructor
  · intro hp
    rcases Nat.lt_trichotomy t n with hlt | rfl | hgt
    · have hcurr : eval (iterBoxBottom n) t = true :=
        (eval_iterBoxBottom_true_iff n t).mpr hlt
      have hnext : eval (□(iterBoxBottom n)) t = true := by
        simpa [iterBoxBottom, eval_box] using
          (eval_iterBoxBottom_true_iff (n + 1) t).mpr (Nat.lt_trans hlt (Nat.lt_succ_self n))
      have hbox : Bitstream.box (eval (iterBoxBottom n)) t = true := by
        simpa [eval_box] using hnext
      have : const0 t = true := by
        simpa [pulseAt, eval, bimplies, hcurr, hbox] using hp
      simp [const0, const] at this
    · rfl
    · have hcurr : eval (iterBoxBottom n) t = false := by
        cases hval : eval (iterBoxBottom n) t with
        | false => exact rfl
        | true =>
            exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt hgt)
              ((eval_iterBoxBottom_true_iff n t).mp hval))
      have hnext : eval (□(iterBoxBottom n)) t = false := by
        cases hval : eval (□(iterBoxBottom n)) t with
        | false => exact rfl
        | true =>
            have : t < n + 1 := by
              simpa [iterBoxBottom, eval_box] using
                (eval_iterBoxBottom_true_iff (n + 1) t).mp hval
            exact False.elim (Nat.not_lt_of_ge (Nat.succ_le_of_lt hgt) this)
      have hbox : Bitstream.box (eval (iterBoxBottom n)) t = false := by
        simpa [eval_box] using hnext
      have : Bitstream.box (eval (iterBoxBottom n)) t = true := by
        have hp' : Bitstream.box (eval (iterBoxBottom n)) t = true := by
          simp [pulseAt, eval, bimplies, hcurr, hbox, const0, const] at hp
        exact hp'
      exact False.elim (by simp [hbox] at this)
  · intro hEq
    subst t
    have hcurr : eval (iterBoxBottom n) n = false := by
      cases hval : eval (iterBoxBottom n) n with
      | false => exact rfl
      | true =>
          exact False.elim (Nat.lt_irrefl n ((eval_iterBoxBottom_true_iff n n).mp hval))
    have hnext : eval (□(iterBoxBottom n)) n = true := by
      simpa [iterBoxBottom, eval_box] using
        (eval_iterBoxBottom_true_iff (n + 1) n).mpr (Nat.lt_succ_self n)
    have hbox : Bitstream.box (eval (iterBoxBottom n)) n = true := by
      simpa [eval_box] using hnext
    simp [pulseAt, eval, bimplies, hcurr, hbox, const0, const]

theorem eval_pulseAt (n : Nat) :
    eval (pulseAt n) = fun t => decide (t = n) := by
  funext t
  by_cases heq : t = n
  · subst t
    have htrue : eval (pulseAt n) n = true := (eval_pulseAt_true_iff n n).mpr rfl
    simp [htrue]
  · have hfalse : eval (pulseAt n) t = false := by
      cases hval : eval (pulseAt n) t with
      | false => exact rfl
      | true =>
          exact False.elim (heq ((eval_pulseAt_true_iff n t).mp hval))
    simp [hfalse, heq]

theorem eval_tailFrom (n : Nat) : eval (tailFrom n) = fun t => decide (n ≤ t) := by
  funext t
  rw [tailFrom, eval_neg, eval_iterBoxBottom]
  by_cases hlt : t < n
  · simp [bnot, hlt, Nat.not_le_of_gt hlt]
  · have hge : n ≤ t := Nat.le_of_not_gt hlt
    simp [bnot, hlt, hge]

theorem eval_encodePrefix (N : Nat) (s : Bitstream) (b : Bit) :
    ∀ n, n ≤ N →
      eval (encodePrefix N s b n) =
        fun t => if t < n then s t else if N ≤ t then b else false := by
  intro n
  induction n with
  | zero =>
      intro hN
      funext t
      by_cases hb : b
      · simp [encodePrefix, hb, eval_tailFrom, Nat.not_lt_zero]
      · simp [encodePrefix, hb, eval_bottom, const0, const, Nat.not_lt_zero]
  | succ n ih =>
      intro hN
      have hnN : n ≤ N := Nat.le_trans (Nat.le_succ n) hN
      have hrest := ih hnN
      funext t
      by_cases hlt : t < n
      · have hpulse : eval (pulseAt n) t = false := by
          rw [eval_pulseAt]
          simp [Nat.ne_of_lt hlt]
        have hrestt : eval (encodePrefix N s b n) t = s t := by
          have := congrArg (fun f => f t) hrest
          simp [hlt] at this
          exact this
        have hlt' : t < n + 1 := Nat.lt_succ_of_lt hlt
        have hNt : ¬ N ≤ t := by
          have : t < N := Nat.lt_of_lt_of_le hlt hnN
          exact Nat.not_le_of_gt this
        by_cases hs : s n
        · rw [encodePrefix, if_pos hs, eval_disj]
          simp [bor, hpulse, hrestt, hlt']
        · simp [encodePrefix, hs, hrestt, hlt']
      · by_cases heq : t = n
        · subst t
          have hpulse : eval (pulseAt n) n = true := by
            rw [eval_pulseAt]
            simp
          have hrestt : eval (encodePrefix N s b n) n = false := by
            have := congrArg (fun f => f n) hrest
            have hNn : ¬ N ≤ n := by
              exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hN)
            simp [hNn] at this
            exact this
          by_cases hs : s n
          · rw [encodePrefix, if_pos hs, eval_disj]
            simp [bor, hpulse, hrestt, hs]
          · simp [encodePrefix, hs, hrestt]
        · have hgt : n < t := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
          have hpulse : eval (pulseAt n) t = false := by
            rw [eval_pulseAt]
            simp [Nat.ne_of_gt hgt]
          have hrestt :
              eval (encodePrefix N s b n) t = (if N ≤ t then b else false) := by
            have := congrArg (fun f => f t) hrest
            have hnotlt : ¬ t < n := Nat.not_lt_of_ge (Nat.le_of_lt hgt)
            simp [hnotlt] at this
            simpa using this
          have hnotlt' : ¬ t < n + 1 := Nat.not_lt_of_ge (Nat.succ_le_of_lt hgt)
          by_cases hs : s n
          · rw [encodePrefix, if_pos hs, eval_disj]
            simp [bor, hpulse, hrestt, hnotlt']
          · simp [encodePrefix, hs, hrestt, hnotlt']

theorem eval_encodeEventuallyConstant (N : Nat) (s : Bitstream) (b : Bit) :
    eval (encodeEventuallyConstant N s b) = fun t => if t < N then s t else b := by
  have hprefix := eval_encodePrefix N s b N (Nat.le_refl N)
  funext t
  have := congrArg (fun f => f t) hprefix
  by_cases hlt : t < N
  · simp [encodeEventuallyConstant, hlt] at this ⊢
    exact this
  · have hge : N ≤ t := Nat.le_of_not_gt hlt
    simp [encodeEventuallyConstant, hlt, hge] at this ⊢
    exact this

end LetterlessFormula

end Bitstream
