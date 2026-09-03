import Mathlib
import P2M.Util
import P2M.Sol.S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute

set_option autoImplicit false

open Module.End

theorem ContinuousLinearMap.map_highPart_orthogonal_le_of_commute {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by p2m_exact_reverting @_root_.P2MW.S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute.solution
