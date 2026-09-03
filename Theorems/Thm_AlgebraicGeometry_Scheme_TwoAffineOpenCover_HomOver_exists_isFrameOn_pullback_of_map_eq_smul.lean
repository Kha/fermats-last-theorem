import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_exists_isFrameOn_pullback_of_map_eq_smul
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.exists_isFrameOn_pullback_of_map_eq_smul
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] {τ : R →+* S}
    {X : Scheme.{u}} {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
    {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of S)}
    (f : HomOver τ 𝒱 c 𝒲 c') (M : X.Modules)
    (s₀ : Γ(M, 𝒱.U0)) (s₁ : Γ(M, 𝒱.U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ 𝒱.U0) (hs₁ : Scheme.Modules.IsFrameOn s₁ 𝒱.U1)
    (t : Γ(X, 𝒱.U0 ⊓ 𝒱.U1))
    (ht : M.presheaf.map (homOfLE inf_le_right).op s₁ = t • M.presheaf.map (homOfLE inf_le_left).op s₀) :
    ∃ (s₀' : Γ((Scheme.Modules.pullback f.hom).obj M, 𝒲.U0))
      (s₁' : Γ((Scheme.Modules.pullback f.hom).obj M, 𝒲.U1)),
      Scheme.Modules.IsFrameOn s₀' 𝒲.U0 ∧ Scheme.Modules.IsFrameOn s₁' 𝒲.U1 ∧
      ((Scheme.Modules.pullback f.hom).obj M).presheaf.map (homOfLE inf_le_right).op s₁' =
        (show Γ(Y, 𝒲.U0 ⊓ 𝒲.U1) from f.map01 t) •
          ((Scheme.Modules.pullback f.hom).obj M).presheaf.map (homOfLE inf_le_left).op s₀' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_exists_isFrameOn_pullback_of_map_eq_smul.solution
