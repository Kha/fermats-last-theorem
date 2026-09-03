import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one
attribute [-instance] M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain
p2m_open "scoped NumberField.PlaceDecomp~subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one"

theorem NumberField.PlaceDecomp.map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F))
    (hunr : Ideal.ramificationIdx' (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) w.asIdeal = 1)
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hρ : ∀ u : Fˣ, ρ.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))
    (b : (F ≃ₐ[E] F) × (F ≃ₐ[E] F) → Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)
    (hb : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))
    (hfin : ∀ g : (F ≃ₐ[E] F) × (F ≃ₐ[E] F), IsOfFinOrder (Additive.toMul (b g) : Fˣ)) :
    (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) ρ 2).hom
      ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
        (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom
          ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom ⟨b, hb⟩)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one.solution
