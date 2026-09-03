import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ConstantReduction_exists_transcendental_residue

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.exists_transcendental_residue
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) [Nonempty (Place L F)] :
    ∃ f : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue f) ∧
      Transcendental L (f : F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_exists_transcendental_residue.solution
