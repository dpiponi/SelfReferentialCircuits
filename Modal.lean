import Bitstream.Streams

namespace Bitstream

theorem box_idempotent_implication_true (s : Bitstream) :
    (box s =⇒ box (box s)) = const1 := by
  funext t
  by_cases h : box s t = true
  · have hbox : box (box s) t = true := by
      rw [box_eq_true_iff_prefix_all_true]
      intro k hk
      apply (box_eq_true_iff_prefix_all_true s k).2
      intro j hj
      exact (box_eq_true_iff_prefix_all_true s t).1 h j (Nat.lt_trans hj hk)
    simp [bimplies, const1, const, h, hbox]
  · have hs : box s t = false := by simpa using h
    simp [bimplies, const1, const, hs]

theorem box_implication_distributes_true (p q : Bitstream) :
    (box (p =⇒ q) =⇒ (box p =⇒ box q)) = const1 := by
  funext t
  by_cases hp : box p t = true
  · by_cases hpq : box (p =⇒ q) t = true
    · have hq : box q t = true := by
        rw [box_eq_true_iff_prefix_all_true]
        intro k hk
        have hpk : p k = true := (box_eq_true_iff_prefix_all_true p t).1 hp k hk
        have himpk : (p =⇒ q) k = true := (box_eq_true_iff_prefix_all_true (p =⇒ q) t).1 hpq k hk
        have : q k = true := by
          simp [bimplies, hpk] at himpk
          exact himpk
        exact this
      simp [bimplies, const1, const, hpq, hp, hq]
    · have hnpq : box (p =⇒ q) t = false := by simpa using hpq
      simp [bimplies, const1, const, hnpq]
  · have hnp : box p t = false := by simpa using hp
    simp [bimplies, const1, const, hnp]

theorem lob_true (s : Bitstream) (h : (box s =⇒ s) = const1) :
    s = const1 := by
  have hpair : ∀ t : Time, box s t = true ∧ s t = true := by
    intro t
    induction t with
    | zero =>
        have hs0 : (box s =⇒ s) 0 = true := by
          simpa [const1, const] using congrArg (fun f => f 0) h
        have hbox0 : box s 0 = true := box_zero s
        have hs : s 0 = true := by
          simpa [bimplies, hbox0] using hs0
        exact ⟨hbox0, hs⟩
    | succ t ih =>
        rcases ih with ⟨hbox, hs⟩
        have hbox' : box s (t + 1) = true := by
          simp [box, hbox, hs]
        have hs' : (box s =⇒ s) (t + 1) = true := by
          simpa [const1, const] using congrArg (fun f => f (t + 1)) h
        have hst : s (t + 1) = true := by
          simpa [bimplies, hbox'] using hs'
        exact ⟨hbox', hst⟩
  funext t
  simpa [const1, const] using (hpair t).2

end Bitstream
