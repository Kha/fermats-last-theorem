import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ConstantReduction_finiteDimensional_and_finrank_adjoin_residue_le

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.finiteDimensional_and_finrank_adjoin_residue_le
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar)
    (f : R.integers) (hf : Transcendental (IsLocalRing.ResidueField A) (R.residue f))
    [FiniteDimensional (IntermediateField.adjoin L ({(f : F)} : Set F)) F] :
    FiniteDimensional
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue f} : Set Fbar)) Fbar ∧
      Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue f} : Set Fbar)) Fbar ≤
        Module.finrank (IntermediateField.adjoin L ({(f : F)} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_finiteDimensional_and_finrank_adjoin_residue_le.solution
