import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) :
    ∃ M : RigidifiedLineBundle (prodStr (pullback.snd f ι) (pullback.snd f ι)) (((L.baseChange ι).prod (L.baseChange ι)).one (𝟙 (Spec (CommRingCat.of R)))) (pullback.snd f ι),
      Nonempty (M.L ≅ ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L) ⊗
      (Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) ⊗
       Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L))))) ∧
      LocIsoOnBase (prodStr (pullback.snd f ι) (pullback.snd f ι))
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift ((L.baseChange ι).one (prodStr (pullback.snd f ι) (pullback.snd f ι))).1 (pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (by rw [((L.baseChange ι).one _).2]))
            (pullback.snd (pullback.snd f ι) (pullback.snd f ι))
            (by rw [pullback.lift_fst_assoc, ((L.baseChange ι).one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr (pullback.snd f ι) (pullback.snd f ι))
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (pullback.fst (pullback.snd f ι) (pullback.snd f ι)) ((L.baseChange ι).one (prodStr (pullback.snd f ι) (pullback.snd f ι))).1 (by rw [((L.baseChange ι).one _).2]))
            (pullback.snd (pullback.snd f ι) (pullback.snd f ι))
            (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr (pullback.snd f ι) (pullback.snd f ι))
        ((Scheme.Modules.pullback
          (pullback.lift (𝟙 _) ((L.baseChange ι).one (prodStr (pullback.snd f ι) (pullback.snd f ι))).1 (by rw [Category.id_comp, ((L.baseChange ι).one _).2]))).obj M.L) (𝟙_ _) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified.solution
