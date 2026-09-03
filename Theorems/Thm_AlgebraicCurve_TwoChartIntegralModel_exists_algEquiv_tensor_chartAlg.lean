import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg

set_option autoImplicit false
open AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

universe u
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg
    (R : Type u) [CommRing R] (K : Type u) [CommRing K] [Algebra R K]
    (F : Type u) [Field F] [Algebra R F] [Algebra K F] [IsScalarTower R K F]
    (M : Submonoid R) [IsLocalization M K] (S : Set F) :
    ∃ e : K ⊗[R] ↥(chartAlg R F S) ≃ₐ[K] ↥(chartAlg K F S),
      ∀ (q : K) (b : ↥(chartAlg R F S)), ((e (q ⊗ₜ b) : ↥(chartAlg K F S)) : F) = q • (b : F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg.solution
