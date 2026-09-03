import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq

set_option autoImplicit false

theorem AutomorphicForm.comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq
    {H P G : Type*} [Group H] [Group P] [Group G]
    (ι : H →* G) (j : H →* P) (θ : P →* G) (hθ : θ.comp j = ι)
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i))
    (f : G → ℂ) (hf : f ∈ ⨆ i, AutomorphicForm.typeSubmodule ι (ρ i)) :
    (fun p : P => f (θ p)) ∈ ⨆ i, AutomorphicForm.typeSubmodule j (ρ i) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_comp_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule_of_comp_eq.solution
