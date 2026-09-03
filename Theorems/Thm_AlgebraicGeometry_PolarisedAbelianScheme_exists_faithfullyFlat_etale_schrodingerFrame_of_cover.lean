import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_etale_schrodingerFrame_of_cover
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)]
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    (S₁ : Type) [CommRing S₁] [Algebra S S₁] [Module.FaithfullyFlat S S₁] [Algebra.Etale S S₁]
    (m : ℕ) (r : Fin m → S₁) (hr : Ideal.span (Set.range r) = ⊤)
    (F : ∀ j : Fin m, SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom ((algebraMap S₁ (Localization.Away (r j))).comp (algebraMap S S₁)))) δ) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧ Algebra.Etale S S' ∧
      Nonempty (SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S S'))) δ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.solution
