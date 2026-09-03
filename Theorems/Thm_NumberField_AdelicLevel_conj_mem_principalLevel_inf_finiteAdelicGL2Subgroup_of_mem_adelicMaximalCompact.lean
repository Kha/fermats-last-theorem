import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem NumberField.AdelicLevel.conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K))
    (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ AutomorphicForm.adelicMaximalCompact K)
    (u : AdelicGL2 (𝓞 K) K)
    (hu : u ∈ principalLevel (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) :
    k * u * k⁻¹ ∈ principalLevel (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact.solution
