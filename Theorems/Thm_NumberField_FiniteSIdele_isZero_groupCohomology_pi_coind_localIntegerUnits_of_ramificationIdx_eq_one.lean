import Mathlib
import Definitions.Def_NumberField_FiniteSIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_FiniteSIdele_isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one
attribute [-simp] Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp
theorem NumberField.FiniteSIdele.isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (V : Set (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∈ V → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (n : ℕ) :
    Limits.IsZero (groupCohomology (GroupCohomology.RepPi.obj fun v : V =>
      Rep.coind (NumberField.FiniteSIdele.D E K v.1).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v.1)) (n + 1)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_FiniteSIdele_isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one.solution
