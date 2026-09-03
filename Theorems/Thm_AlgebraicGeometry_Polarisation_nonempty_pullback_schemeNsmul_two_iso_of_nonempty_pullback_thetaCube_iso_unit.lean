import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι)
    (h : Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.lift (𝟙 _) (𝟙 _) rfl) (negMor (pullback.snd f ι) (L.baseChange ι))
          (by rw [pullback.lift_fst_assoc, Category.id_comp, negMor_over]))).obj
        ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L) ⊗
      (Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) ⊗
       Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)))) ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅
      (N.L ⊗ N.L ⊗ N.L) ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f ι) (L.baseChange ι))).obj N.L) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit.solution
