import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective
import P2M.Util
import P2M.Sol.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
    {H K G : Type*} [Group H] [Group K] [Group G]
    (j : H →* K) (ι' : H →* G) (hι' : Function.Injective ι')
    (C : Submodule ℂ (K → ℂ)) (hC : ∀ (k : H) (u : K → ℂ), u ∈ C → (fun κ => u (κ * j k)) ∈ C)
    (A : ↥C →ₗ[ℂ] (G → ℂ))
    (hA : ∀ (k : H) (u : ↥C) (x : G),
      A ⟨fun κ => (u : K → ℂ) (κ * j k), hC k u u.2⟩ x = A u (x * ι' k))
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i)) (u : K → ℂ) (hu : u ∈ C)
    (hut : u ∈ ⨆ i, typeSubmodule j (ρ i)) :
    A ⟨u, hu⟩ ∈ ⨆ i, typeSubmodule ι' (ρ i) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective.solution
