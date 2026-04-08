import Bitstream.Magari
import Bitstream.Guarded
import Bitstream.Completeness

/-
This module packages the main theorems of the bitstream development in a form
close to the intended paper narrative.

The central interpretation is:

- `Bitstream` is the history of a signal through discrete time.
- `box` is the delayed-latch operator from the paper, not an ordinary shift.
- guarded one-variable formulas denote causal operators on bitstreams.

The main consequences proved in the imported modules are:

1. Every guarded one-variable formula has a semantic fixed point.
2. That fixed point is unique.
3. The unique fixed point is realized by a letterless formula.
4. The induced modal operator satisfies Löb's principle in the bitstream model.

Thus guarded self-reference in this setting is not paradoxical re-entry but
well-defined delayed feedback with a unique behavior.
-/
namespace Bitstream

namespace Results

/--
Every guarded one-variable formula has a semantic fixed point.
-/
theorem guarded_fixedPoint_exists (φ : GuardedFormula) :
    GuardedFormula.HasSemanticFixedPoint φ :=
  GuardedFormula.solve_hasSemanticFixedPoint φ

/--
Every guarded one-variable formula has a unique semantic fixed point.
-/
theorem guarded_fixedPoint_unique
    (φ : GuardedFormula)
    {s t : Bitstream}
    (hs : GuardedFormula.eval φ s = s)
    (ht : GuardedFormula.eval φ t = t) :
    s = t :=
  GuardedFormula.fixedPoint_unique φ hs ht

/--
Every guarded one-variable formula has a letterless fixed point.
-/
theorem guarded_letterless_fixedPoint (φ : GuardedFormula) :
    GuardedFormula.HasLetterlessFixedPoint φ :=
  GuardedFormula.hasLetterlessFixedPoint φ

/--
Every letterless formula denotes an eventually constant bitstream.
-/
theorem letterless_eventuallyConstant (a : LetterlessFormula) :
    EventuallyConstant (LetterlessFormula.eval a) := by
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
  simpa [heq] using hstable

/--
Completeness for the letterless fragment:
if a letterless formula denotes the constantly true bitstream, then it is provable.
-/
theorem letterless_completeness (a : LetterlessFormula)
    (h : LetterlessFormula.eval a = const1) :
    Provable a :=
  Bitstream.completeness a h

/--
Soundness and completeness for the letterless fragment.
-/
theorem letterless_provable_iff_true (a : LetterlessFormula) :
    Provable a ↔ LetterlessFormula.eval a = const1 :=
  Bitstream.provable_iff_eval_const1 a

/--
Eventually constant bitstreams carry a Magari algebra structure.
-/
def eventuallyConstant_magari : MagariAlgebra :=
  eventuallyConstantMagari

/--
Integers carry the transported Magari algebra structure induced by their
identification with eventually constant bitstreams.
-/
noncomputable def integer_magari : MagariAlgebra :=
  integerMagari

/--
Integers embed injectively into the Magari algebra of eventually constant bitstreams.
-/
theorem int_embedding_injective : Function.Injective intToECBitstream :=
  intToECBitstream_injective

/--
Every eventually constant bitstream is represented by a unique integer.
-/
theorem eventuallyConstant_has_integer (s : ECBitstream) :
    ∃ z : Int, intToECBitstream z = s ∧
      ∀ w : Int, intToECBitstream w = s → w = z := by
  refine ⟨ecBitstreamToInt s, ecBitstreamToInt_spec s, ?_⟩
  intro w hw
  exact intToECBitstream_injective (hw.trans (ecBitstreamToInt_spec s).symm)

/--
The integer embedding respects bitwise complement.
-/
theorem int_embedding_not (z : Int) :
    intToECBitstream (~~~z) = ECBitstream.neg (intToECBitstream z) :=
  intToECBitstream_not z

/--
The transported integer negation agrees with ordinary bitwise complement.
-/
theorem int_neg_eq_not (z : Int) :
    intNeg z = ~~~z :=
  intNeg_eq_not z

/--
The transported integer xor operation agrees with xor at the bitstream level.
-/
theorem int_xor_semantics (z w : Int) :
    intToECBitstream (intXor z w) =
      ECBitstream.sup
        (ECBitstream.inf (intToECBitstream z) (ECBitstream.neg (intToECBitstream w)))
        (ECBitstream.inf (ECBitstream.neg (intToECBitstream z)) (intToECBitstream w)) :=
  intToECBitstream_intXor z w

/--
On integers, the transported modal operator is given by the xor-with-successor
bit-hack formula.
-/
theorem int_box_eq_xor_add_one (z : Int) :
    intBox z = intXor z (z + 1) :=
  intBox_eq_intXor_add_one z

/--
Semantic Löb theorem for bitstreams:
if `□s → s` is constantly true, then `s` is constantly true.
-/
theorem lob_semantic (s : Bitstream) (h : (box s =⇒ s) = const1) :
    s = const1 :=
  lob_true s h

/--
Formula-level Löb theorem for letterless formulas.
-/
theorem lob_letterless (a : LetterlessFormula)
    (h : LetterlessFormula.eval (LetterlessFormula.imp (LetterlessFormula.box a) a) = const1) :
    LetterlessFormula.eval a = const1 :=
  LetterlessFormula.eval_lob a h

/--
Formula-level Löb theorem for one-variable formulas under any environment.
-/
theorem lob_oneLetter (p : Bitstream) (φ : OneLetterFormula)
    (h : OneLetterFormula.eval p (OneLetterFormula.imp (OneLetterFormula.box φ) φ) = const1) :
    OneLetterFormula.eval p φ = const1 :=
  OneLetterFormula.eval_lob p φ h

end Results

end Bitstream
