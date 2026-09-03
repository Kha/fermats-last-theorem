import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_law_baseChange_comp_eq_of_comp_eq
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_law_baseChange_comp_eq_of_comp_eq
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] [Algebra S S'] [Algebra S S''] [Algebra S' S'']
    [IsScalarTower S S' S'']
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))))
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    ∃ L'' : RelativeGroupLaw S'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'')))),
      (∀ (T : Scheme.{0}) (t'' : T ⟶ Spec (CommRingCat.of S''))
          (P Q : SchemeHomOver t'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))),
          (L''.mul t'' P Q).1 ≫
              pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) ≫
                  Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
                (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                  ← IsScalarTower.algebraMap_eq]) =
            (L'.mul (t'' ≫ Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
              ⟨P.1 ≫ pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))
                  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) ≫
                    Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
                  (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    ← IsScalarTower.algebraMap_eq]),
                by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))
                  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) ≫
                    Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
                  (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    ← IsScalarTower.algebraMap_eq]),
                by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ (T : Scheme.{0}) (t'' : T ⟶ Spec (CommRingCat.of S''))
          (P Q : SchemeHomOver t'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))),
          (L''.mul t'' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) =
            (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'')))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_law_baseChange_comp_eq_of_comp_eq.solution
