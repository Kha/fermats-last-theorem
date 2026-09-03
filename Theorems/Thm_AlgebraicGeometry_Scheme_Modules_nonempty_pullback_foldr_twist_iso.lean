import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso
attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_foldr_twist_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) {m : ℕ} (K : Fin m → Y.IdealSheafData) (pos neg : Fin m → ℕ)
    {ι : Type*} [Fintype ι] (C : ι → Y.IdealSheafData) (aplus aminus : ι → ℕ)
    (hK : ∀ j, (K j).IsInvertible) (hC : ∀ F, (C F).IsInvertible)
    (hK' : ∀ j, ((K j).comap f).IsInvertible) (hC' : ∀ F, ((C F).comap f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj
        ((List.finRange m).foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N)
          ((∏ F, C F ^ aplus F).invModule ⊗ (∏ F, C F ^ aminus F).module)) ≅
      (List.finRange m).foldr (fun j N => ((K j).comap f ^ pos j).invModule ⊗ ((K j).comap f ^ neg j).module ⊗ N)
        ((∏ F, (C F).comap f ^ aplus F).invModule ⊗ (∏ F, (C F).comap f ^ aminus F).module)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso.solution
