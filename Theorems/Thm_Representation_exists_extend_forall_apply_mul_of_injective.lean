import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_extend_forall_apply_mul_of_injective

set_option autoImplicit false

universe u v w

theorem Representation.exists_extend_forall_apply_mul_of_injective
    {H : Type u} {G : Type v} [Group H] [Group G] {W : Type w} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ k : H, ∀ v ∈ P, ρ k v ∈ P)
    (T : P →ₗ[ℂ] (G → ℂ))
    (hT : ∀ (k : H) (v : P) (x : G), T ⟨ρ k v, hP k v v.2⟩ x = T v (x * ι k)) :
    ∃ T' : W →ₗ[ℂ] (G → ℂ),
      (∀ (k : H) (v : W) (x : G), T' (ρ k v) x = T' v (x * ι k)) ∧ ∀ v : P, T' v = T v := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_extend_forall_apply_mul_of_injective.solution
