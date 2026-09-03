import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_mulEquiv_pt_eq_and_isScalarElt_iff_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.exists_mulEquiv_pt_eq_and_isScalarElt_iff_of_iso
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓕 𝓕' : A.Modules) (ι : 𝓕 ≅ 𝓕') :
    ∃ τ : thetaGroup f L hc 𝓕 ≃* thetaGroup f L hc 𝓕',
      (∀ g : thetaGroup f L hc 𝓕, thetaGroup.pt f L hc 𝓕' (τ g) = thetaGroup.pt f L hc 𝓕 g) ∧
      (∀ (g : thetaGroup f L hc 𝓕) (c : k),
        thetaGroup.IsScalarElt f L hc 𝓕 g c ↔ thetaGroup.IsScalarElt f L hc 𝓕' (τ g) c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_mulEquiv_pt_eq_and_isScalarElt_iff_of_iso.solution
