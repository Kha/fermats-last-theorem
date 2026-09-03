import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_SchrodingerFrame_exists_sigma_eq_baseScalar_smul_of_isUnit

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

universe u

theorem AlgebraicGeometry.Polarisation.SchrodingerFrame.exists_sigma_eq_baseScalar_smul_of_isUnit
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {𝓛 : A.Modules} {R : Type u} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    {g : ℕ} {δ : Fin g → ℕ} [hδ : ∀ i, NeZero (δ i)]
    (F : Polarisation.SchrodingerFrame f L 𝓛 t δ) (c : R) (hc : IsUnit c) :
    ∃ F' : Polarisation.SchrodingerFrame f L 𝓛 t δ,
      (∀ h, F'.σ h = Polarisation.baseScalar f t c • F.σ h) ∧ F'.lift = F.lift ∧ F'.dualLift = F.dualLift := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_SchrodingerFrame_exists_sigma_eq_baseScalar_smul_of_isUnit.solution
