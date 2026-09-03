import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_withFullLevel_packages

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_withFullLevel_packages
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (m : ℕ) (hm : 3 ≤ m) (S : Type) [CommRing S] (hm' : IsUnit ((m : ℕ) : S)) :
    ∀ (X : PolarisedAbelianScheme 2 36 m S) (s : QMStructure Λ star β X),
        ∃ u : FakeEllipticCurve.WithFullLevel Λ 1 m S, s.Packages u := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_withFullLevel_packages.solution
