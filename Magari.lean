import Bitstream.Modal

namespace Bitstream

structure MagariAlgebra where
  Carrier : Type
  top : Carrier
  bot : Carrier
  neg : Carrier → Carrier
  inf : Carrier → Carrier → Carrier
  sup : Carrier → Carrier → Carrier
  imp : Carrier → Carrier → Carrier
  box : Carrier → Carrier
  box_implication_distributes_top :
    ∀ p q : Carrier, imp (box (imp p q)) (imp (box p) (box q)) = top
  box_idempotent_implication_top :
    ∀ p : Carrier, imp (box p) (box (box p)) = top
  lob :
    ∀ p : Carrier, imp (box p) p = top → p = top

/-
Eventually constant bitstreams are the natural carrier for the integer-style
presentation: they are closed under the Boolean operations and under `box`.
-/
def ECBitstream : Type := { s : Bitstream // EventuallyConstant s }

namespace ECBitstream

instance : CoeFun ECBitstream (fun _ => Time → Bit) where
  coe s := s.1

def of (s : Bitstream) (hs : EventuallyConstant s) : ECBitstream := ⟨s, hs⟩

def bot : ECBitstream := ⟨const0, const0_eventuallyConstant⟩
def top : ECBitstream := ⟨const1, const1_eventuallyConstant⟩

def neg (s : ECBitstream) : ECBitstream := ⟨∼s.1, bnot_eventuallyConstant s.2⟩
def inf (s t : ECBitstream) : ECBitstream := ⟨s.1 &&& t.1, band_eventuallyConstant s.2 t.2⟩
def sup (s t : ECBitstream) : ECBitstream := ⟨s.1 ||| t.1, bor_eventuallyConstant s.2 t.2⟩
def imp (s t : ECBitstream) : ECBitstream := ⟨s.1 =⇒ t.1, bimplies_eventuallyConstant s.2 t.2⟩
def box (s : ECBitstream) : ECBitstream := ⟨Bitstream.box s.1, box_eventuallyConstant s.1⟩

prefix:max "∼ₑ" => neg
infixr:70 " &&&ₑ " => inf
infixr:65 " |||ₑ " => sup
infixr:60 " =⇒ₑ " => imp
prefix:max "□ₑ" => box

@[ext] theorem ext {s t : ECBitstream} (h : ∀ u, s u = t u) : s = t := by
  cases s with
  | mk s hs =>
      cases t with
      | mk t ht =>
          simp at h
          have hst : s = t := funext h
          subst hst
          rfl

theorem top_apply (t : Time) : top t = true := rfl

theorem bot_apply (t : Time) : bot t = false := rfl

theorem box_implication_distributes_top (p q : ECBitstream) :
    (□ₑ (p =⇒ₑ q) =⇒ₑ (□ₑ p =⇒ₑ □ₑ q)) = top := by
  ext t
  simpa [imp, box, top] using congrArg (fun f => f t) (box_implication_distributes_true p.1 q.1)

theorem box_idempotent_implication_top (p : ECBitstream) :
    (□ₑ p =⇒ₑ □ₑ (□ₑ p)) = top := by
  ext t
  simpa [imp, box, top] using congrArg (fun f => f t) (box_idempotent_implication_true p.1)

theorem lob (p : ECBitstream) (h : (□ₑ p =⇒ₑ p) = top) : p = top := by
  ext t
  have hp : p.1 = const1 := by
    apply lob_true
    funext u
    have := congrArg (fun f => f u) h
    simpa [imp, box, top] using this
  simpa [top, const1, const] using congrArg (fun f => f t) hp

end ECBitstream

def eventuallyConstantMagari : MagariAlgebra where
  Carrier := ECBitstream
  top := ECBitstream.top
  bot := ECBitstream.bot
  neg := ECBitstream.neg
  inf := ECBitstream.inf
  sup := ECBitstream.sup
  imp := ECBitstream.imp
  box := ECBitstream.box
  box_implication_distributes_top := ECBitstream.box_implication_distributes_top
  box_idempotent_implication_top := ECBitstream.box_idempotent_implication_top
  lob := ECBitstream.lob

def intStream : Int → Bitstream
  | Int.ofNat n => fun t => n.testBit t
  | Int.negSucc n => fun t => !(n.testBit t)

theorem nat_testBit_false_of_ge (n t : Nat) (ht : n ≤ t) : n.testBit t = false := by
  apply Nat.testBit_lt_two_pow
  have hpow : 2 ^ n ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
  exact Nat.lt_of_lt_of_le Nat.lt_two_pow_self hpow

theorem natStream_eventuallyConstant (n : Nat) : EventuallyConstant (fun t => n.testBit t) := by
  refine ⟨n, false, ?_⟩
  intro t ht
  exact nat_testBit_false_of_ge n t ht

theorem intStream_eventuallyConstant (z : Int) : EventuallyConstant (intStream z) := by
  cases z with
  | ofNat n =>
      exact natStream_eventuallyConstant n
  | negSucc n =>
      exact bnot_eventuallyConstant (natStream_eventuallyConstant n)

def intToECBitstream (z : Int) : ECBitstream := ⟨intStream z, intStream_eventuallyConstant z⟩

theorem intStream_not (z : Int) : intStream (~~~z) = ∼(intStream z) := by
  cases z with
  | ofNat n =>
      funext t
      rfl
  | negSucc n =>
      funext t
      change n.testBit t = !(!(n.testBit t))
      simp

theorem intToECBitstream_not (z : Int) :
    intToECBitstream (~~~z) = ∼ₑ (intToECBitstream z) := by
  ext t
  simp [intToECBitstream, ECBitstream.neg, intStream_not]

theorem intStream_injective : Function.Injective intStream := by
  intro z w h
  cases z with
  | ofNat n =>
      cases w with
      | ofNat m =>
          have hbits : ∀ i, n.testBit i = m.testBit i := by
            intro i
            exact congrFun h i
          exact congrArg Int.ofNat (Nat.eq_of_testBit_eq hbits)
      | negSucc m =>
          let t := max n m + 1
          have : False := by
            have hft : false = true := by
              simpa [intStream, t, nat_testBit_false_of_ge,
                Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _),
                Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)] using congrFun h t
            cases hft
          exact False.elim this
  | negSucc n =>
      cases w with
      | ofNat m =>
          let t := max n m + 1
          have : False := by
            have hft : true = false := by
              simpa [intStream, t, nat_testBit_false_of_ge,
                Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _),
                Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)] using congrFun h t
            cases hft
          exact False.elim this
      | negSucc m =>
          have hbits : ∀ i, n.testBit i = m.testBit i := by
            intro i
            have hi : !(n.testBit i) = !(m.testBit i) := by
              simpa [intStream] using congrFun h i
            cases hn : n.testBit i <;> cases hm : m.testBit i <;> simp [hn, hm] at hi ⊢
          exact congrArg Int.negSucc (Nat.eq_of_testBit_eq hbits)

theorem intToECBitstream_injective : Function.Injective intToECBitstream := by
  intro z w h
  exact intStream_injective (congrArg Subtype.val h)

def natPrefix : Nat → Bitstream → Nat
  | 0, _ => 0
  | n + 1, s => natPrefix n s + if s n then 2 ^ n else 0

theorem natPrefix_lt_two_pow (n : Nat) (s : Bitstream) : natPrefix n s < 2 ^ n := by
  induction n with
  | zero =>
      simp [natPrefix]
  | succ n ih =>
      by_cases hs : s n
      · simp [natPrefix, hs]
        have hle : natPrefix n s ≤ 2 ^ n - 1 := Nat.le_pred_of_lt ih
        omega
      · simp [natPrefix, hs]
        have hpow : 2 ^ n < 2 ^ (n + 1) := by
          rw [Nat.pow_succ']
          omega
        exact Nat.lt_trans ih hpow

theorem natPrefix_testBit_of_lt (n : Nat) (s : Bitstream) {t : Nat} (ht : t < n) :
    (natPrefix n s).testBit t = s t := by
  induction n generalizing t with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ ht)
  | succ n ih =>
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with
      | inl hlt =>
          by_cases hs : s n
          · rw [natPrefix, if_pos hs, Nat.add_comm, Nat.testBit_two_pow_add_gt hlt]
            exact ih hlt
          · simp [natPrefix, hs, ih hlt]
      | inr heq =>
          subst t
          have hfalse : (natPrefix n s).testBit n = false := by
            exact Nat.testBit_lt_two_pow (natPrefix_lt_two_pow n s)
          by_cases hs : s n
          · rw [natPrefix, if_pos hs, Nat.add_comm, Nat.testBit_two_pow_add_eq]
            simp [hfalse, hs]
          · simp [natPrefix, hs, hfalse]

theorem natPrefix_testBit_false_of_ge (n : Nat) (s : Bitstream) {t : Nat} (ht : n ≤ t) :
    (natPrefix n s).testBit t = false := by
  apply Nat.testBit_lt_two_pow
  have hpow : 2 ^ n ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
  exact Nat.lt_of_lt_of_le (natPrefix_lt_two_pow n s) hpow

theorem exists_int_of_eventuallyConstant (s : Bitstream) (hs : EventuallyConstant s) :
    ∃ z : Int, intStream z = s := by
  rcases hs with ⟨N, b, hb⟩
  cases b with
  | false =>
      refine ⟨Int.ofNat (natPrefix N s), ?_⟩
      funext t
      by_cases ht : t < N
      · simpa [intStream] using natPrefix_testBit_of_lt N s ht
      · have hNt : N ≤ t := Nat.le_of_not_gt ht
        have hsfalse : s t = false := hb t hNt
        have hprefix : (natPrefix N s).testBit t = false :=
          natPrefix_testBit_false_of_ge N s hNt
        simpa [intStream, hsfalse] using hprefix
  | true =>
      refine ⟨Int.negSucc (natPrefix N (∼s)), ?_⟩
      funext t
      by_cases ht : t < N
      · have hprefix : (natPrefix N (∼s)).testBit t = (∼s) t :=
          natPrefix_testBit_of_lt N (∼s) ht
        simp [intStream, bnot, hprefix]
      · have hNt : N ≤ t := Nat.le_of_not_gt ht
        have hstrue : s t = true := hb t hNt
        have hprefix : (natPrefix N (∼s)).testBit t = false :=
          natPrefix_testBit_false_of_ge N (∼s) hNt
        simp [intStream, hprefix, hstrue]

theorem intStream_surjective_on_eventuallyConstant (s : ECBitstream) :
    ∃ z : Int, intToECBitstream z = s := by
  rcases exists_int_of_eventuallyConstant s.1 s.2 with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  ext t
  simpa [intToECBitstream] using congrArg (fun f => f t) hz

noncomputable def ecBitstreamToInt (s : ECBitstream) : Int :=
  Classical.choose (intStream_surjective_on_eventuallyConstant s)

theorem ecBitstreamToInt_spec (s : ECBitstream) :
    intToECBitstream (ecBitstreamToInt s) = s :=
  Classical.choose_spec (intStream_surjective_on_eventuallyConstant s)

theorem ecBitstream_equiv_int (s : ECBitstream) :
    intToECBitstream (ecBitstreamToInt s) = s :=
  ecBitstreamToInt_spec s

theorem ecBitstreamToInt_right_inverse (z : Int) :
    ecBitstreamToInt (intToECBitstream z) = z := by
  apply intToECBitstream_injective
  exact ecBitstreamToInt_spec (intToECBitstream z)

def intTop : Int := Int.negSucc 0
def intBot : Int := 0

noncomputable def intNeg (z : Int) : Int :=
  ecBitstreamToInt (ECBitstream.neg (intToECBitstream z))

noncomputable def intInf (z w : Int) : Int :=
  ecBitstreamToInt (ECBitstream.inf (intToECBitstream z) (intToECBitstream w))

noncomputable def intSup (z w : Int) : Int :=
  ecBitstreamToInt (ECBitstream.sup (intToECBitstream z) (intToECBitstream w))

noncomputable def intImp (z w : Int) : Int :=
  ecBitstreamToInt (ECBitstream.imp (intToECBitstream z) (intToECBitstream w))

noncomputable def intBox (z : Int) : Int :=
  ecBitstreamToInt (ECBitstream.box (intToECBitstream z))

noncomputable def intXor (z w : Int) : Int :=
  intSup (intInf z (intNeg w)) (intInf (intNeg z) w)

theorem intToECBitstream_intNeg (z : Int) :
    intToECBitstream (intNeg z) = ECBitstream.neg (intToECBitstream z) := by
  simp [intNeg, ecBitstreamToInt_spec]

theorem intToECBitstream_intInf (z w : Int) :
    intToECBitstream (intInf z w) =
      ECBitstream.inf (intToECBitstream z) (intToECBitstream w) := by
  simp [intInf, ecBitstreamToInt_spec]

theorem intToECBitstream_intSup (z w : Int) :
    intToECBitstream (intSup z w) =
      ECBitstream.sup (intToECBitstream z) (intToECBitstream w) := by
  simp [intSup, ecBitstreamToInt_spec]

theorem intToECBitstream_intImp (z w : Int) :
    intToECBitstream (intImp z w) =
      ECBitstream.imp (intToECBitstream z) (intToECBitstream w) := by
  simp [intImp, ecBitstreamToInt_spec]

theorem intToECBitstream_intBox (z : Int) :
    intToECBitstream (intBox z) = ECBitstream.box (intToECBitstream z) := by
  simp [intBox, ecBitstreamToInt_spec]

theorem intToECBitstream_intXor (z w : Int) :
    intToECBitstream (intXor z w) =
      ECBitstream.sup
        (ECBitstream.inf (intToECBitstream z) (ECBitstream.neg (intToECBitstream w)))
        (ECBitstream.inf (ECBitstream.neg (intToECBitstream z)) (intToECBitstream w)) := by
  simp [intXor, intToECBitstream_intSup, intToECBitstream_intInf, intToECBitstream_intNeg]

theorem intStream_zero_eq_decide_mod_two (z : Int) : intStream z 0 = decide (z % 2 = 1) := by
  cases z with
  | ofNat n =>
      cases hm : n % 2 with
      | zero =>
          simp [intStream, Nat.testBit_zero, hm]
          omega
      | succ k =>
          have hk : k = 0 := by omega
          subst hk
          simp [intStream, Nat.testBit_zero, hm]
          omega
  | negSucc n =>
      have hneg : (Int.negSucc n) % 2 = 1 - (n : Int) % 2 := by
        simpa using (Int.negSucc_emod n (b := 2) (by decide : (0 : Int) < 2))
      cases hm : n % 2 with
      | zero =>
          simp [intStream, Nat.testBit_zero, hneg, hm]
          omega
      | succ k =>
          have hk : k = 0 := by omega
          subst hk
          simp [intStream, Nat.testBit_zero, hneg, hm]
          omega

theorem intStream_succ_zero (z : Int) : intStream (z + 1) 0 = !(intStream z 0) := by
  rw [intStream_zero_eq_decide_mod_two, intStream_zero_eq_decide_mod_two]
  by_cases h : z % 2 = 1
  · have hs : (z + 1) % 2 = 0 := by
      have hdecomp : 2 * (z / 2) + z % 2 = z := by
        simpa [Int.mul_comm] using (Int.mul_ediv_add_emod z 2)
      have hdecomp' : 2 * ((z + 1) / 2) + (z + 1) % 2 = z + 1 := by
        simpa [Int.mul_comm] using (Int.mul_ediv_add_emod (z + 1) 2)
      have hlt : (z + 1) % 2 < 2 := Int.emod_lt_of_pos (z + 1) (by decide : (0 : Int) < 2)
      have hnonneg : 0 ≤ (z + 1) % 2 := Int.emod_nonneg (z + 1) (by decide : (2 : Int) ≠ 0)
      omega
    simp [h, hs]
  · have hz0 : z % 2 = 0 := by
      have hlt : z % 2 < 2 := Int.emod_lt_of_pos z (by decide : (0 : Int) < 2)
      have hnonneg : 0 ≤ z % 2 := Int.emod_nonneg z (by decide : (2 : Int) ≠ 0)
      omega
    have hs : (z + 1) % 2 = 1 := by
      have hdecomp : 2 * (z / 2) + z % 2 = z := by
        simpa [Int.mul_comm] using (Int.mul_ediv_add_emod z 2)
      have hdecomp' : 2 * ((z + 1) / 2) + (z + 1) % 2 = z + 1 := by
        simpa [Int.mul_comm] using (Int.mul_ediv_add_emod (z + 1) 2)
      have hlt : (z + 1) % 2 < 2 := Int.emod_lt_of_pos (z + 1) (by decide : (0 : Int) < 2)
      have hnonneg : 0 ≤ (z + 1) % 2 := Int.emod_nonneg (z + 1) (by decide : (2 : Int) ≠ 0)
      omega
    simp [hz0, hs]

theorem intStream_shiftRight_one (z : Int) (t : Nat) : intStream (z >>> 1) t = intStream z (t + 1) := by
  cases z with
  | ofNat n =>
      change (n / 2).testBit t = n.testBit (t + 1)
      simpa using (Nat.testBit_add n t 1).symm
  | negSucc n =>
      rw [Int.negSucc_shiftRight]
      simp [intStream, Nat.add_comm]

theorem shiftRight_add_one (z : Int) :
    (z + 1) >>> 1 = z >>> 1 + if intStream z 0 then 1 else 0 := by
  rw [Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow, intStream_zero_eq_decide_mod_two]
  by_cases h : z % 2 = 1
  · simp [h]
    have hdecomp : 2 * (z / 2) + z % 2 = z := by
      simpa [Int.mul_comm] using (Int.mul_ediv_add_emod z 2)
    omega
  · have hmod0 : z % 2 = 0 := by
      have hlt : z % 2 < 2 := Int.emod_lt_of_pos z (by decide : (0 : Int) < 2)
      have hnonneg : 0 ≤ z % 2 := Int.emod_nonneg z (by decide : (2 : Int) ≠ 0)
      omega
    simp [hmod0]
    have hdecomp : 2 * (z / 2) + z % 2 = z := by
      simpa [Int.mul_comm] using (Int.mul_ediv_add_emod z 2)
    omega

theorem box_shift_of_head_true {s : Bitstream} (h0 : s 0 = true) (t : Nat) :
    box s (t + 1) = box (fun u => s (u + 1)) t := by
  have hiff : box s (t + 1) = true ↔ box (fun u => s (u + 1)) t = true := by
    rw [box_eq_true_iff_prefix_all_true, box_eq_true_iff_prefix_all_true]
    constructor
    · intro hs k hk
      exact hs (k + 1) (Nat.succ_lt_succ hk)
    · intro hs k hk
      cases k with
      | zero =>
          simpa using h0
      | succ k =>
          have hk' : k < t := Nat.lt_of_succ_lt_succ hk
          simpa using hs k hk'
  by_cases h : box s (t + 1) = true
  · have h' : box (fun u => s (u + 1)) t = true := hiff.mp h
    simp [h, h']
  · have h' : box (fun u => s (u + 1)) t = false := by
      by_cases hb : box (fun u => s (u + 1)) t = true
      · exact False.elim (h (hiff.mpr hb))
      · cases hx : box (fun u => s (u + 1)) t <;> simp [hx] at hb ⊢
    simp [h, h']

theorem intStream_succ_eq_xor_box (z : Int) (t : Nat) :
    intStream (z + 1) t = (intStream z t != box (intStream z) t) := by
  induction t generalizing z with
  | zero =>
      simpa [box_zero] using intStream_succ_zero z
  | succ t ih =>
      cases h0 : intStream z 0 with
      | false =>
          have hbox1 : box (intStream z) 1 = false := box_succ_of_input_false h0
          have hbox : box (intStream z) (t + 1) = false := by
            simpa [Nat.add_comm] using box_stays_false hbox1 t
          have hsr : (z + 1) >>> 1 = z >>> 1 := by
            simpa [h0] using shiftRight_add_one z
          rw [← intStream_shiftRight_one (z + 1) t, hsr, hbox]
          simp [intStream_shiftRight_one]
      | true =>
          have hsr : (z + 1) >>> 1 = z >>> 1 + 1 := by
            simpa [h0] using shiftRight_add_one z
          have hbox : box (intStream z) (t + 1) = box (intStream (z >>> 1)) t := by
            rw [box_shift_of_head_true h0]
            congr
            funext u
            symm
            exact intStream_shiftRight_one z u
          rw [← intStream_shiftRight_one (z + 1) t, hsr, hbox]
          simpa [intStream_shiftRight_one] using ih (z >>> 1)

theorem intBox_eq_intXor_add_one (z : Int) : intBox z = intXor z (z + 1) := by
  apply intToECBitstream_injective
  rw [intToECBitstream_intBox, intToECBitstream_intXor]
  ext t
  change box (intStream z) t =
    ((intStream z t && !(intStream (z + 1) t)) || (!(intStream z t) && intStream (z + 1) t))
  have hs : intStream (z + 1) t = (intStream z t != box (intStream z) t) :=
    intStream_succ_eq_xor_box z t
  rw [hs]
  cases hz : intStream z t <;> cases hb : box (intStream z) t <;> decide

theorem intTop_eq : intTop = -1 := rfl
theorem intBot_eq : intBot = 0 := rfl

theorem intToECBitstream_intTop : intToECBitstream intTop = ECBitstream.top := by
  calc
    intToECBitstream intTop = intToECBitstream (~~~ (0 : Int)) := by rfl
    _ = ECBitstream.neg (intToECBitstream (0 : Int)) := intToECBitstream_not 0
    _ = ECBitstream.top := by
      ext t
      simp [ECBitstream.neg, intToECBitstream, intStream, ECBitstream.top, const1, const, bnot]

theorem intToECBitstream_intBot : intToECBitstream intBot = ECBitstream.bot := by
  ext t
  simp [intBot, intToECBitstream, intStream, ECBitstream.bot, const0, const]

theorem intNeg_eq_not (z : Int) : intNeg z = ~~~z := by
  apply intToECBitstream_injective
  rw [intToECBitstream_intNeg, intToECBitstream_not]

noncomputable def integerMagari : MagariAlgebra where
  Carrier := Int
  top := intTop
  bot := intBot
  neg := intNeg
  inf := intInf
  sup := intSup
  imp := intImp
  box := intBox
  box_implication_distributes_top := by
    intro p q
    apply intToECBitstream_injective
    simpa [intToECBitstream_intImp, intToECBitstream_intBox, intToECBitstream_intTop] using
      ECBitstream.box_implication_distributes_top (intToECBitstream p) (intToECBitstream q)
  box_idempotent_implication_top := by
    intro p
    apply intToECBitstream_injective
    simpa [intToECBitstream_intImp, intToECBitstream_intBox, intToECBitstream_intTop] using
      ECBitstream.box_idempotent_implication_top (intToECBitstream p)
  lob := by
    intro p hp
    apply intToECBitstream_injective
    rw [intToECBitstream_intTop]
    have hp' : ECBitstream.imp (ECBitstream.box (intToECBitstream p)) (intToECBitstream p) =
        ECBitstream.top := by
      simpa [intToECBitstream_intImp, intToECBitstream_intBox, intToECBitstream_intTop] using
        congrArg intToECBitstream hp
    exact ECBitstream.lob (intToECBitstream p) hp'


end Bitstream
