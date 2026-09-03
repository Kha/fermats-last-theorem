import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛 : X.Modules}
    (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓛 f N) (hσ : Scheme.Modules.IsSectionBasis f 𝓛 𝔓.σ) :
    IsClosedImmersion 𝔓.toProj := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections.solution
