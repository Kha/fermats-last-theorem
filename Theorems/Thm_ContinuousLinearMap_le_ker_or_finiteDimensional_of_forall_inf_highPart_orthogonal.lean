import Mathlib
import P2M.Util
import P2M.Sol.S_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal

set_option autoImplicit false

open Module.End

theorem ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
    (hX : ∀ r : ℝ, 0 < r → X ⊓ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ ∨ X ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ) :
    X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) ∨ FiniteDimensional 𝕜 ↥X := by p2m_exact_reverting @_root_.P2MW.S_ContinuousLinearMap_le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal.solution
