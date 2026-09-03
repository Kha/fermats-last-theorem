import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_exists_forall_nonempty_pullback_iso_of_isPullback_pi_localizationAway
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.exists_forall_nonempty_pullback_iso_of_isPullback_pi_localizationAway
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M M' : X.Modules)
    (h : LocIsoOnBase f M M') :
    ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧
      ∀ (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))) (c : X' ⟶ X),
        IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i))))) →
        Nonempty ((Scheme.Modules.pullback c).obj M ≅ (Scheme.Modules.pullback c).obj M') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_exists_forall_nonempty_pullback_iso_of_isPullback_pi_localizationAway.solution
