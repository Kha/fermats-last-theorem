import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_ideal_fg_forall_isPullback_exists_comp_toProj_eq_one_comp_iff_map_eq_bot
attribute [-simp] AlgebraicGeometry.ProjSpace.linSubst_X AlgebraicGeometry.ProjSpace.linSubst_C

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_exists_comp_toProj_eq_one_comp_iff_map_eq_bot
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hU : IsUnit U) :
    ∃ J : Ideal S, J.FG ∧ ∀ (T : Type) [CommRing T] (φ : S →+* T) (Y : FramedPolarisedAbelianScheme g N n T),
      FramedPolarisedAbelianScheme.IsPullback φ X Y →
      ∀ (P' : Scheme.Modules.ProjPresentation Y.pol Y.f N),
        (∀ i : Fin (N + 1), P'.σ i =
          ∑ j : Fin (N + 1), ((Y.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (φ (U i j)))) • Y.frame.σ j) →
        ((∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) Y.f, x.1 ≫ Y.frame.toProj = (Y.L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ P'.toProj) ↔
          J.map φ = ⊥) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_ideal_fg_forall_isPullback_exists_comp_toProj_eq_one_comp_iff_map_eq_bot.solution
