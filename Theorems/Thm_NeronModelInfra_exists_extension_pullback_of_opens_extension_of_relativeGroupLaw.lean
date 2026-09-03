import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_extension_pullback_of_opens_extension_of_relativeGroupLaw
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
theorem NeronModelInfra.exists_extension_pullback_of_opens_extension_of_relativeGroupLaw
    (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [(Ideal.span {(p : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(p : ℤ)})]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw ℤ g)
    (η : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))))
    (hη : (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base η = IsLocalRing.closedPoint R)
    (hirr : ∀ x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x = IsLocalRing.closedPoint R → η ⤳ x)
    (φη : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))))
    (φK : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶
      pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (θ : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
    (hθ₁ : θ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) =
      pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫
        pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hθ₂ : θ ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) =
      pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (hφ : φK ≫ θ = θ ≫ φη.1)
    (V : (pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).Opens)
    (v : (V : Scheme.{0}) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hv : v ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) =
      V.ι ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hVη : ∀ x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hηV : η ∈ V)
    (hle : Set.range (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))).base ⊆ Set.range V.ι.base)
    (hlift : IsOpenImmersion.lift V.ι
        (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) hle ≫ v =
      φK ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) :
    ∃ gA : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) ⟶ G,
      gA ≫ g = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) ≫ g ∧
      ∀ j : pullback g (specGenericFibreInclusion ℤ ℚ) ⟶
          pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))),
        j ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) =
          pullback.fst g (specGenericFibreInclusion ℤ ℚ) →
        j ≫ gA = φη.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_extension_pullback_of_opens_extension_of_relativeGroupLaw.solution
