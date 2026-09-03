import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_BilinForm_orthogonal_le_of_similitude_of_forall_map_sub_mem

theorem LinearMap.BilinForm.orthogonal_le_of_similitude_of_forall_map_sub_mem
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : ∀ w : V, (∀ x : V, B x w = 0) → w = 0)
    (V₀ : Submodule K V) (g : V →ₗ[K] V) (hg : Function.Surjective g)
    (ε : K) (hε : ε ≠ 1)
    (hsim : ∀ x y : V, B (g x) (g y) = ε * B x y)
    (hmove : ∀ x : V, g x - x ∈ V₀) :
    B.orthogonal V₀ ≤ V₀ := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_BilinForm_orthogonal_le_of_similitude_of_forall_map_sub_mem.solution
