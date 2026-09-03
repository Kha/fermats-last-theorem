import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_JacJ1_ChartAlgebra
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing

open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_algEquiv_rat_tensor_chartAlg_chartRing
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (S : Set ↥(modularFunctionFieldFull N)) :
    ∃ e : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S) ≃ₐ[ℚ]
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ S),
      ∀ (q : ℚ) (b : ↥(chartAlg N ℓ S)),
        ((e (q ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing ℚ S)) : ↥(modularFunctionFieldFull N))
          = q • (b : ↥(modularFunctionFieldFull N)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing.solution
