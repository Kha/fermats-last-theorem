import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (P' : Scheme.Modules.ProjPresentation X.pol X.f N) :
    (∃ θ : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))), ∀ i : Fin (N + 1),
        θ.act (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
            Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤)) =
          (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (P'.σ i) :
            Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
              (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))) ↔
    (∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f,
        Polarisation.translate X.f X.L (𝟙 (Spec (CommRingCat.of S))) x ≫ pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫
            X.frame.toProj =
          pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ P'.toProj) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq.solution
