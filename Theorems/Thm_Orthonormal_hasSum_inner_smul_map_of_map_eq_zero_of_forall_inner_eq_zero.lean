import Mathlib
import P2M.Util
import P2M.Sol.S_Orthonormal_hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero

set_option autoImplicit false

open scoped InnerProductSpace

theorem Orthonormal.hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} (b : ι → E) (hb : Orthonormal 𝕜 b) (T : E →L[𝕜] F)
    (hT : ∀ v : E, (∀ i, ⟪b i, v⟫_𝕜 = 0) → T v = 0) (u : E) :
    HasSum (fun i => ⟪b i, u⟫_𝕜 • T (b i)) (T u) := by p2m_exact_reverting @_root_.P2MW.S_Orthonormal_hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero.solution
