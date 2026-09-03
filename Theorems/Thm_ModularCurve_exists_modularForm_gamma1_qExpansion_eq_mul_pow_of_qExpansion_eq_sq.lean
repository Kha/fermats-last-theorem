import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq

set_option autoImplicit false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq
    (M : ℕ) [NeZero M] (k : ℕ) (w : ModularForm (Gamma1 M) 1)
    (X : LaurentSeries ℂ)
    (hX : X ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))
    (F₂ : ModularForm (Gamma1 M) (2 * (k : ℤ)))
    (hF₂ : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 F₂) =
      (X * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 w) ^ k) ^ 2) :
    ∃ f : ModularForm (Gamma1 M) (k : ℤ),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) =
        X * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 w) ^ k := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq.solution
