import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_regularProlongation_of_transcendental

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.exists_regularProlongation_of_transcendental
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (f : F) (htrL : Transcendental L f)
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F] :
    ∃ (W : ValuationSubring F)
      (_ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField W))
      (R : RegularProlongation A F (IsLocalRing.ResidueField W)),
      R.integers = W ∧ ∃ hfR : f ∈ R.integers,
        Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.solution
