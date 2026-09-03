import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_map_mumfordBundle
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

theorem AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_iso_pullback_map_mumfordBundle
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (α : A ⟶ A) (hα : α ≫ f = f)
    (hαhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt α hα (L.mul t P Q) = L.mul t (pushPt α hα P) (pushPt α hα Q))
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N) :
    Nonempty (mumfordBundle f L ((Scheme.Modules.pullback α).obj N) ≅
      (Scheme.Modules.pullback
        (pullback.map f f f f α α (𝟙 _) (by rw [Category.comp_id, hα]) (by rw [Category.comp_id, hα]))).obj
          (mumfordBundle f L N)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_map_mumfordBundle.solution
