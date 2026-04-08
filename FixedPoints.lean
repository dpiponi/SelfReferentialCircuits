import Bitstream.Modal

namespace Bitstream

theorem fixedPoint_box_is_const1 (p : Bitstream) (h : p = box p) : p = const1 := by
  funext t
  induction t with
  | zero =>
      have hp : p 0 = box p 0 := congrFun h 0
      simpa [box, const1, const] using hp
  | succ t ih =>
      have hp : p (t + 1) = box p (t + 1) := congrFun h (t + 1)
      have hpt : p t = true := by simpa [const1, const] using ih
      have hboxpt : box p t = true := by
        simpa [hpt] using (congrFun h t).symm
      have hsucc : box p (t + 1) = true := by
        simp [box, hboxpt, hpt]
      have : p (t + 1) = true := by
        exact hp.trans hsucc
      simpa [const1, const] using this

theorem const1_is_fixedPoint_box : box const1 = const1 := box_const1

theorem fixedPoint_box_unique (p : Bitstream) : p = box p ↔ p = const1 := by
  constructor
  · intro h
    exact fixedPoint_box_is_const1 p h
  · intro h
    rw [h]
    exact box_const1.symm

theorem fixedPoint_box_box_is_const1 (p : Bitstream) (h : p = box (box p)) : p = const1 := by
  funext t
  have hpair : ∀ u : Time, p u = true ∧ box p u = true := by
    intro u
    induction u with
    | zero =>
        constructor
        · have hp0 : p 0 = box (box p) 0 := congrFun h 0
          simpa [box] using hp0
        · simp [box]
    | succ u ihu =>
        rcases ihu with ⟨hpu, hboxu⟩
        constructor
        · have hpu1 : p (u + 1) = box (box p) (u + 1) := congrFun h (u + 1)
          have hboxboxu : box (box p) u = true := by
            exact Eq.trans (congrFun h u).symm hpu
          have : box (box p) (u + 1) = true := by
            simp [box, hboxboxu, hboxu]
          exact hpu1.trans this
        · have hpdef : p u = true := hpu
          simp [box, hboxu, hpdef]
  simpa [const1, const] using (hpair t).1

set_option linter.unnecessarySimpa false in
theorem fixedPoint_box_box_unique (p : Bitstream) : p = box (box p) ↔ p = const1 := by
  constructor
  · intro h
    exact fixedPoint_box_box_is_const1 p h
  · intro h
    rw [h]
    simpa [box_const1] using box_const1.symm

theorem mutualFixedPoint_box_is_const1 (p q : Bitstream) (hp : p = box q) (hq : q = box p) :
    p = const1 ∧ q = const1 := by
  have hpp : p = box (box p) := by
    calc
      p = box q := hp
      _ = box (box p) := by rw [hq]
  have hp1 : p = const1 := fixedPoint_box_box_is_const1 p hpp
  have hq1 : q = const1 := by rw [hq, hp1]; exact box_const1
  exact ⟨hp1, hq1⟩

theorem pulse_eq_box_not_pulse : pulse = box (∼pulse) := by
  funext t
  cases t with
  | zero =>
      rfl
  | succ t =>
      cases t with
      | zero =>
          simp [pulse, box, bnot]
      | succ t =>
          have hnot0 : (∼pulse) 0 = false := by simp [bnot, pulse]
          have hbox1 : box (∼pulse) 1 = false := by simp [box, hnot0]
          have hboxn : box (∼pulse) (Nat.succ (Nat.succ t)) = false := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using box_stays_false hbox1 (t + 1)
          simpa [pulse] using hboxn

theorem fixedPoint_box_not_is_pulse (p : Bitstream) (h : p = box (∼p)) : p = pulse := by
  funext t
  cases t with
  | zero =>
      have hp0 : p 0 = box (∼p) 0 := congrFun h 0
      simpa [box, pulse] using hp0
  | succ t =>
      cases t with
      | zero =>
          have hp1 : p 1 = box (∼p) 1 := congrFun h 1
          have hp0 : p 0 = true := by
            have := congrFun h 0
            simpa [box] using this
          have hnot0 : (∼p) 0 = false := by
            simp [bnot, hp0]
          have hbox1 : box (∼p) 1 = false := by simp [box, hnot0]
          exact hp1.trans hbox1
      | succ t =>
          have hp2 : p (Nat.succ (Nat.succ t)) = box (∼p) (Nat.succ (Nat.succ t)) := congrFun h (Nat.succ (Nat.succ t))
          have hp0 : p 0 = true := by
            have := congrFun h 0
            simpa [box] using this
          have hnot0 : (∼p) 0 = false := by
            simp [bnot, hp0]
          have hbox1 : box (∼p) 1 = false := by
            simp [box, hnot0]
          have hboxn : box (∼p) (Nat.succ (Nat.succ t)) = false := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using box_stays_false hbox1 (t + 1)
          simpa [pulse] using hp2.trans hboxn

theorem fixedPoint_box_not_unique (p : Bitstream) : p = box (∼p) ↔ p = pulse := by
  constructor
  · intro h
    exact fixedPoint_box_not_is_pulse p h
  · intro h
    rw [h]
    exact pulse_eq_box_not_pulse

end Bitstream
