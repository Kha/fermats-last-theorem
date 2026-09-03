import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1

set_option autoImplicit false
open NumberField
open scoped NumberField.InfPlaceDecomp
theorem NumberField.InfPlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1 (E K : Type) [Field E] [Field K] [Algebra E K]
    (w : InfinitePlace K) [Fintype (NumberField.InfPlaceDecomp.decomp E K w)] :
    Nat.card (Rep.ofMulDistribMulAction (NumberField.InfPlaceDecomp.decomp E K w) (w.Completion)ˣ).tateH0 =
      Nat.card (NumberField.InfPlaceDecomp.decomp E K w) ∧
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.InfPlaceDecomp.decomp E K w) (w.Completion)ˣ).tateHneg1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1.solution
