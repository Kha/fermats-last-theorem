import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
    {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛 : X.Modules}
    {M N : ℕ} (𝔔 : Scheme.Modules.ProjPresentation 𝓛 f M) (𝔓 : Scheme.Modules.ProjPresentation 𝓛 f N)
    (hspan : ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → S,
      𝔔.σ j = ∑ k, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (a k))) • 𝔓.σ k)
    (hQ : IsClosedImmersion 𝔔.toProj) :
    IsClosedImmersion 𝔓.toProj := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul.solution
