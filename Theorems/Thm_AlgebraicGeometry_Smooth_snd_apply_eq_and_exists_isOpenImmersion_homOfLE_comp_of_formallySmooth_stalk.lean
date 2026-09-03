import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
attribute [-instance] NeronModelInfra.ComponentReading.isDomain NeronModelInfra.MinimalComponentData.finite NeronModelInfra.ComponentReading.isDiscreteValuationRing NeronModelInfra.ComponentReading.locallyOfFiniteType NeronModelInfra.ComponentReading.smooth NeronModelInfra.MinimalComponentData.nonempty NeronModelInfra.ComponentReading.isOpenImmersion NeronModelInfra.ModelFamily.isOpenImmersion_chart PresheafOfModules.ExteriorPower.instModulePresheafAb
attribute [-simp] NeronModelInfra.MinimalComponentData.mk.injEq NeronModelInfra.ComponentReading.mk.injEq NeronModelInfra.ComponentReading.mk.sizeOf_spec NeronModelInfra.MinimalComponentData.mk.sizeOf_spec NeronModelInfra.pointGenericFibre_coe_comp_fst NeronModelInfra.pointGenericFibre_coe_comp_snd NeronModelInfra.ModelFamily.mk.injEq NeronModelInfra.ModelFamily.mk.sizeOf_spec NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z X Y : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) [Smooth z] [Smooth f] [Smooth g] [LocallyOfFiniteType g]
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
    (yT : ↑Y) (hyT : g.base yT = IsLocalRing.closedPoint R)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z g) (hv₁ : v ≫ pullback.fst z g = U₀.ι ≫ pullback.fst z f)
    (hgen : yT ⤳ (v ≫ pullback.snd z g).base ⟨η, hηU⟩)
    (hdom : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
    (hdom' : IsDomain ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)))
    (hfrac : letI : Algebra ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
    (hfs : letI : Algebra ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :
    (v ≫ pullback.snd z g).base ⟨η, hηU⟩ = yT ∧
      ∃ (U₁ : (pullback z f).Opens) (_ : η ∈ U₁) (h₁ : U₁ ≤ U₀),
        IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk.solution
