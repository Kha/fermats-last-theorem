import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1
    (N : ℕ) [NeZero N] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1.solution
