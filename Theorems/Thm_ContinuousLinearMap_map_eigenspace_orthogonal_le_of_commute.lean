import Mathlib
import P2M.Util
import P2M.Sol.S_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute

set_option autoImplicit false

open Module.End
open scoped InnerProductSpace

theorem ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    (S : E →L[𝕜] E) (hST : S.comp T = T.comp S) (μ : 𝕜) (hμ : μ ≠ 0) :
    (eigenspace (T : Module.End 𝕜 E) μ).map (S : Module.End 𝕜 E) ≤ eigenspace (T : Module.End 𝕜 E) μ ∧
    ((eigenspace (T : Module.End 𝕜 E) μ)ᗮ).map (S : Module.End 𝕜 E) ≤ (eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by p2m_exact_reverting @_root_.P2MW.S_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute.solution
