import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_CuspFormClass_isZeroAt_slash_of_mem_Gamma0
import P2M.Util
namespace P2MW.S_CuspForm_stableD

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    CuspForm.StableD M H k := by
  intro σ f c hc
  exact CuspFormClass.isZeroAt_slash_of_mem_Gamma0 M H k σ f hc
