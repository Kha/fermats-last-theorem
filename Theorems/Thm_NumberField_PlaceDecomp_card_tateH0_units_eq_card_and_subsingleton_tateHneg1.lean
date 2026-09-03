import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp
theorem NumberField.PlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1 (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K))
    [Fintype (NumberField.PlaceDecomp.decomp E K w)] [IsCyclic (NumberField.PlaceDecomp.decomp E K w)] :
    Nat.card (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ).tateH0 =
      Nat.card (NumberField.PlaceDecomp.decomp E K w) ∧
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ).tateHneg1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1.solution
