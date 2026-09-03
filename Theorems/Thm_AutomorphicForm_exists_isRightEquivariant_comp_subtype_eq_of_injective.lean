import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective
    {H G : Type*} [Group H] [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H W)
    (A : Submodule ℂ W) (hA : ∀ (k : H) (a : W), a ∈ A → ρ k a ∈ A)
    (TA : ↥A →ₗ[ℂ] (G → ℂ))
    (hTA : ∀ (k : H) (a : ↥A) (x : G), TA ⟨ρ k a, hA k a a.2⟩ x = TA a (x * ι k)) :
    ∃ T : W →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ T ∧ T ∘ₗ A.subtype = TA := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective.solution
