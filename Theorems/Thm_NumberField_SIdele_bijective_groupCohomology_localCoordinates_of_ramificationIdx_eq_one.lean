import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one
attribute [-simp] Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (n : ℕ) :
    Function.Bijective (fun x : groupCohomology (NumberField.SIdele.obj E K S) (n + 1) =>
      ((fun v : {v // v ∈ S} =>
          (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
              (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) (n + 1) ≫
            (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) (n + 1)).hom).hom x),
       (fun v : InfinitePlace E =>
          (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
              (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inr v)) (n + 1) ≫
            (groupCohomology.coindIso (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)) (n + 1)).hom).hom x))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one.solution
