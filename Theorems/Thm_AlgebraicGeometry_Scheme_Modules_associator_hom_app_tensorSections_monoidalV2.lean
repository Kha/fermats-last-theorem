import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.associator_hom_app_tensorSections_monoidalV2
    {X : Scheme.{u}} {L M N : X.Modules} {U : X.Opens} (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    (α_ L M N).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections (L := L ⊗ M) (M := N)
          (AlgebraicGeometry.Scheme.Modules.tensorSections l m) n) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (L := L) (M := M ⊗ N) l
        (AlgebraicGeometry.Scheme.Modules.tensorSections m n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2.solution
