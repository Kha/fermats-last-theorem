import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛 : X.Modules}
    (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓛 f N) (hσ : Scheme.Modules.IsSectionBasis f 𝓛 𝔓.σ) :
    IsClosedImmersion 𝔓.toProj := by
  obtain ⟨M, 𝔔, hQ⟩ := hva
  exact AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul 𝔔 𝔓
    (fun j => by obtain ⟨a, ha⟩ := hσ.2 (𝔔.σ j); exact ⟨a, ha.symm⟩) hQ
