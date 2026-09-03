import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_compConst_eq_of_t_eq_sum

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.compConst_eq_of_t_eq_sum (p : ℕ) [Fact p.Prime] {r : ℕ} (Φ Φ' : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (U : Matrix (Fin r) (Fin r) ℚ) (hUunit : IsUnit U)
    (hU : ∀ i j, 0 ≤ padicValRat p (U i j) ∨ U i j = 0)
    (hUinv : ∀ i j, 0 ≤ padicValRat p (U⁻¹ i j) ∨ U⁻¹ i j = 0)
    (ht : ∀ i, Φ'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j) :
    compConst Φ' s hs = compConst Φ s hs := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_compConst_eq_of_t_eq_sum.solution
