import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero
    {H G : Type*} [Group H] [Group G] (ι : H →* G) (hι : Function.Injective ι)
    {I : Type*} [Fintype I] {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i))
    (f : G → ℂ) :
    f ∈ (⨆ i, typeSubmodule ι (ρ i)) ↔
      ∀ a : H →₀ ℂ, (∀ i, (a.sum fun k c => c • (ρ i k)) = 0) →
        (fun x : G => a.sum fun k c => c * f (x * ι k)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero.solution
