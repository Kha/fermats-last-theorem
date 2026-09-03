import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isFrameOn_pullback_stage_of_map_eq_smul
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isFrameOn_pullback_stage_of_map_eq_smul
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    {A₀ A' : Type u} [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] (φ : A₀ →ₐ[R] A')
    (M : (Limits.pullback c (specMap R A₀)).Modules)
    (s₀ : Γ(M, (𝒱.pullback c A₀).U0)) (s₁ : Γ(M, (𝒱.pullback c A₀).U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ (𝒱.pullback c A₀).U0)
    (hs₁ : Scheme.Modules.IsFrameOn s₁ (𝒱.pullback c A₀).U1)
    (t : Γ(Limits.pullback c (specMap R A₀), (𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1))
    (ht : M.presheaf.map (homOfLE inf_le_right).op s₁ = t • M.presheaf.map (homOfLE inf_le_left).op s₀) :
    ∃ (s₀' : Γ((Scheme.Modules.pullback (HomOver.stage 𝒱 c φ).hom).obj M, (𝒱.pullback c A').U0))
      (s₁' : Γ((Scheme.Modules.pullback (HomOver.stage 𝒱 c φ).hom).obj M, (𝒱.pullback c A').U1)),
      Scheme.Modules.IsFrameOn s₀' (𝒱.pullback c A').U0 ∧ Scheme.Modules.IsFrameOn s₁' (𝒱.pullback c A').U1 ∧
      ((Scheme.Modules.pullback (HomOver.stage 𝒱 c φ).hom).obj M).presheaf.map (homOfLE inf_le_right).op s₁' =
        (show Γ(Limits.pullback c (specMap R A'), (𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1) from
          (HomOver.stage 𝒱 c φ).map01 t) •
        ((Scheme.Modules.pullback (HomOver.stage 𝒱 c φ).hom).obj M).presheaf.map (homOfLE inf_le_left).op s₀' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isFrameOn_pullback_stage_of_map_eq_smul.solution
