import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one

set_option autoImplicit false
open NumberField M4aHerbrand

theorem NumberField.TateGlobal.forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one
    (F : Type) [Field F] [NumberField F] :
    ∀ x : ↥(NumberField.TateGlobal.normOneIdeles F) ⧸
        (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F),
      x ≠ 1 → ∃ χ : (↥(NumberField.TateGlobal.normOneIdeles F) ⧸
          (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F)) →* ℂˣ,
        Continuous χ ∧ χ x ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one.solution
