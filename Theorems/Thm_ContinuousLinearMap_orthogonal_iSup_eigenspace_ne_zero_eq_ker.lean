import Mathlib
import P2M.Util
import P2M.Sol.S_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker

set_option autoImplicit false

open Module.End

theorem ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) := by p2m_exact_reverting @_root_.P2MW.S_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker.solution
