import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_finiteBySections_tensorPow_of_forall_geometricFibre
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_finiteBySections_tensorPow_of_forall_geometricFibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hfin : ∀ (𝒰 : X.OrderedAffineCover) (n : ℕ), (OModulePresheaf.ofModules f (L.tensorPow n)).CechFinite 𝒰)
    (hfib : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K], ∃ n : ℕ,
      Scheme.Modules.FiniteBySections
          ((Scheme.Modules.pullback
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj (L.tensorPow n))
          (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      ∀ 𝒲 : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).OrderedAffineCover,
        Subsingleton
          ((OModulePresheaf.ofModules (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
              ((Scheme.Modules.pullback
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj
                (L.tensorPow n))).HSucc 𝒲 0)) :
    ∃ n : ℕ, Scheme.Modules.FiniteBySections (L.tensorPow n) f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_finiteBySections_tensorPow_of_forall_geometricFibre.solution
