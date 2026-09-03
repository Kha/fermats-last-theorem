import Mathlib
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem NumberField.AdelicLevel.centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ N)
    (t : (v.adicCompletion K)ˣ) (ht : Valued.v (t : v.adicCompletion K) = 1) :
    AutomorphicForm.centralScalar (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) ∈
      principalLevel (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup.solution
