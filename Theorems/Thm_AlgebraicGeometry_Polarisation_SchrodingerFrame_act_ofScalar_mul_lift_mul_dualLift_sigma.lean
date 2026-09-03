import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_SchrodingerFrame_act_ofScalar_mul_lift_mul_dualLift_sigma

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.Polarisation.SchrodingerFrame.act_ofScalar_mul_lift_mul_dualLift_sigma
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (ω : R) (hω : ω ^ (2 * d) = 1)
    (F : SchrodingerFrame f L 𝓛 t δ) (z : ThetaLevel.Heis δ d)
    (χ : AddChar (ThetaLevel.HH δ) R) (hχ : ∀ y, χ y = ThetaLevel.thetaChar δ d R ω z.k y)
    (c : Rˣ) (hc : (c : R) = ThetaLevel.omegaPow d R ω z.a) (y : ThetaLevel.HH δ) :
    (ThetaPt.ofScalar c * F.lift z.h * F.dualLift χ).act (F.σ y) =
      baseScalar f t (ThetaLevel.omegaPow d R ω (z.a + ThetaLevel.pair δ d z.k y)) • F.σ (y + z.h) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_SchrodingerFrame_act_ofScalar_mul_lift_mul_dualLift_sigma.solution
