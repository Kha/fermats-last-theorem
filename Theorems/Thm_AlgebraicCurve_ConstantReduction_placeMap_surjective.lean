import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ConstantReduction_placeMap_surjective

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.placeMap_surjective
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) [HasPrincipalDivisors L F] :
    Function.Surjective R.placeMap := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_placeMap_surjective.solution
