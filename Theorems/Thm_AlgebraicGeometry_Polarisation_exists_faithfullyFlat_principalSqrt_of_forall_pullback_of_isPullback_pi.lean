import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_forall_pullback_of_isPullback_pi
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_forall_pullback_of_isPullback_pi
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of (∀ i, C i))) (L' : RelativeGroupLaw (∀ i, C i) f')
    (𝓛 : A'.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {Ai : Fin k → Scheme.{0}} (fi : ∀ i, Ai i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Ai i ⟶ A')
    (hv : ∀ i, IsPullback (v i) (fi i) f' (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (Li : ∀ i, RelativeGroupLaw (C i) (fi i))
    (hLi : ∀ (i : Fin k) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of (C i))) (P Q : SchemeHomOver t (fi i)),
      ((Li i).mul t P Q).1 ≫ v i =
        (L'.mul (t ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)))
          ⟨P.1 ≫ v i, by rw [Category.assoc, (hv i).w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ v i, by rw [Category.assoc, (hv i).w, ← Category.assoc, Q.2]⟩).1)
    (h : ∀ i, (∃ (S' : Type) (_ : CommRing S') (_ : Algebra (C i) S'),
      Module.FaithfullyFlat (C i) S' ∧
      ∀ (L'' : RelativeGroupLaw S' (pullback.snd (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S'))))),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S'))))),
            (L''.mul t' P Q).1 ≫ pullback.fst (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S'))) =
              ((Li i).mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap (C i) S'))))
                ⟨P.1 ≫ pullback.fst (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S')))) L'' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S'))))
            ((Scheme.Modules.pullback (pullback.fst (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S'))))).obj ((Scheme.Modules.pullback (v i)).obj 𝓛))
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd (fi i) (Spec.map (CommRingCat.ofHom (algebraMap (C i) S')))) L'')).obj 𝓛₀))) :
    (∃ (S' : Type) (_ : CommRing S') (_ : Algebra (∀ i, C i) S'),
      Module.FaithfullyFlat (∀ i, C i) S' ∧
      ∀ (L'' : RelativeGroupLaw S' (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S'))))),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S'))))),
            (L''.mul t' P Q).1 ≫ pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S'))) =
              (L'.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S'))))
                ⟨P.1 ≫ pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S')))) L'' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S'))))
            ((Scheme.Modules.pullback (pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S'))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap (∀ i, C i) S')))) L'')).obj 𝓛₀)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_forall_pullback_of_isPullback_pi.solution
