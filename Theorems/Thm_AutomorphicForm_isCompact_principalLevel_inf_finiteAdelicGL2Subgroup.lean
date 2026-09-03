import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm~isCompact_levelOne_inf_finiteAdelicGL2Subgroup"

theorem AutomorphicForm.isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    IsCompact ((principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isCompact_principalLevel_inf_finiteAdelicGL2Subgroup.solution
