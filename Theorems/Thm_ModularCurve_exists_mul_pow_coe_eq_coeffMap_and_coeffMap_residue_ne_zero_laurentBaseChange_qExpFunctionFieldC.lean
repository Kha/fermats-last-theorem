import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_mul_pow_coe_eq_coeffMap_and_coeffMap_residue_ne_zero_laurentBaseChange_qExpFunctionFieldC

set_option autoImplicit false
open scoped MatrixGroups

theorem ModularCurve.exists_mul_pow_coe_eq_coeffMap_and_coeffMap_residue_ne_zero_laurentBaseChange_qExpFunctionFieldC
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (n : ℕ) (hn : 0 < n)
    (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hf : f ≠ 0) :
    ∃ (h : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
      (y : LaurentSeries ↥A),
      h ≠ 0 ∧
      ((f * h ^ n : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
          LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap A.subtype y ∧
      ModularCurve.coeffMap (IsLocalRing.residue ↥A) y ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_mul_pow_coe_eq_coeffMap_and_coeffMap_residue_ne_zero_laurentBaseChange_qExpFunctionFieldC.solution
