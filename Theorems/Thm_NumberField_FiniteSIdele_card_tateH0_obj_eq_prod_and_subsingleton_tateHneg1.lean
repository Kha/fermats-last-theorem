import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_NumberField_FiniteSIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_FiniteSIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp
theorem NumberField.FiniteSIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1 (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] [IsCyclic (K ≃ₐ[E] K)] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hSram : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    Nat.card (NumberField.FiniteSIdele.obj E K S).tateH0 = ∏ v ∈ S, Nat.card (NumberField.FiniteSIdele.D E K v) ∧
    Subsingleton (NumberField.FiniteSIdele.obj E K S).tateHneg1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_FiniteSIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1.solution
