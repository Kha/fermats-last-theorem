import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion

theorem ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ)) :
    ∃ (D : ℤ) (p : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp ((D : ℂ) • (⇑f : UpperHalfPlane → ℂ)) p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.solution
