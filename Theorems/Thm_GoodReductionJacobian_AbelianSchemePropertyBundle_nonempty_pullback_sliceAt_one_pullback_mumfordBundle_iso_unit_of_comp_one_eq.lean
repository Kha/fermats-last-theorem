import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
    {B : Type} [CommRing B] [IsLocalRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (hA : AbelianSchemePropertyBundle B f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (u v : A ⟶ A) (hu : u ≫ f = f) (hv : v ≫ f = f)
    (hue : (L.one (𝟙 (Spec (CommRingCat.of B)))).1 ≫ u = (L.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (hve : (L.one (𝟙 (Spec (CommRingCat.of B)))).1 ≫ v = (L.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (w : pullback f f ⟶ pullback f f)
    (hw₁ : w ≫ pullback.fst f f = pullback.fst f f ≫ u) (hw₂ : w ≫ pullback.snd f f = pullback.snd f f ≫ v) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))))).obj
        ((Scheme.Modules.pullback w).obj (mumfordBundle f L 𝓛)) ≅ 𝟙_ _) ∧
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj
          ((Scheme.Modules.pullback w).obj (mumfordBundle f L 𝓛))) ≅ 𝟙_ _) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq.solution
