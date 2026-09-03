import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_SheafOfModules_MonoidalV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M : A.Modules} (σ : M ⟶ M) (c : k) (h : IsConstScalar f σ c) (K : A.Modules) :
    IsConstScalar f (σ ▷ K) c ∧ IsConstScalar f (K ◁ σ) c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2.solution
