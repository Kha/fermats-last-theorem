import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (N : ℕ) [NeZero N] :
    HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion (N : ℝ) (⇑f : UpperHalfPlane → ℂ)) =
      ModularCurve.qExpand ℂ N
        (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f : UpperHalfPlane → ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods.solution
