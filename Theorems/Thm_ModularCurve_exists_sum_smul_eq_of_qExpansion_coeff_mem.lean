import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem
    (N : ℕ) [NeZero N] {k : ℤ} (K₀ : IntermediateField ℚ ℂ)
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ K₀) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, c i ∈ K₀) ∧ (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem.solution
