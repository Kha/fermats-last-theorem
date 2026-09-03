import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support

set_option autoImplicit false

open scoped ComplexConjugate
p2m_open "NumberField AutomorphicForm~matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp"

theorem AutomorphicForm.star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (S : Subgroup (AdelicGL2 (𝓞 F) F))
    (hS : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), rowIsometryInclAt₀ F w k ∈ S)
    (E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hEfd : FiniteDimensional ℂ E)
    (hER : ∀ s ∈ S, ∀ v ∈ E, (fun x => v (x * s)) ∈ E)
    (hsupp : ∀ v ∈ E, ∀ x : AdelicGL2 (𝓞 F) F, v x ≠ 0 → x ∈ S)
    (hcont : ∀ v ∈ E, ∀ (w : InfinitePlace F) (x : AdelicGL2 (𝓞 F) F),
      Continuous fun k : rowIsometrySubgroup₀ w.Completion => v (x * rowIsometryInclAt₀ F w k))
    (hEt : E ≤ archCutSubmodule F tys) :
    ∀ v ∈ E, (fun x => conj (v x⁻¹)) ∈ archCutSubmodule F tys := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support.solution
