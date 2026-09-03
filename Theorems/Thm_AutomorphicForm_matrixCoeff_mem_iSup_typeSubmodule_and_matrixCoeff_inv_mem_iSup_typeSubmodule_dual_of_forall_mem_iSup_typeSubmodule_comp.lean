import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp

set_option autoImplicit false

theorem AutomorphicForm.matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp
    {G Kc H : Type*} [Group G] [Group Kc] [Group H] (ι : Kc →* G) (j : H →* Kc)
    (hj : Function.Injective j) (E : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ E]
    (hE : ∀ κ : Kc, ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)
    {J : Type*} {W : J → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i))
    (hEρ : ∀ v ∈ E, v ∈ ⨆ i, AutomorphicForm.typeSubmodule (ι.comp j) (ρ i))
    (lam : Module.Dual ℂ E) (v : E) :
    (fun κ : Kc => lam ⟨fun x => (v : G → ℂ) (x * ι κ), hE κ v v.2⟩) ∈
        ⨆ i, AutomorphicForm.typeSubmodule j (ρ i) ∧
      (fun κ : Kc => lam ⟨fun x => (v : G → ℂ) (x * ι κ⁻¹), hE κ⁻¹ v v.2⟩) ∈
        ⨆ i, AutomorphicForm.typeSubmodule j (ρ i).dual := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp.solution
