import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_ArchIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1

set_option autoImplicit false
open NumberField
open scoped NumberField.InfPlaceDecomp
theorem NumberField.ArchIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1 (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] :
    Nat.card (NumberField.ArchIdele.obj E K).tateH0 =
      ∏ v : InfinitePlace E, Nat.card (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) ∧
    Subsingleton (NumberField.ArchIdele.obj E K).tateHneg1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_ArchIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1.solution
