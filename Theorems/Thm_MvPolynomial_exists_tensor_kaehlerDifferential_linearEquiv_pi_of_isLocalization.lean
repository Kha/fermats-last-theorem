import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization

set_option autoImplicit false

open MvPolynomial TensorProduct KaehlerDifferential

theorem MvPolynomial.exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P]
    (K : Type) [CommRing K] [Algebra P K] [Algebra (MvPolynomial (Fin n) R) K]
    [IsScalarTower (MvPolynomial (Fin n) R) P K] :
    ∃ e : K ⊗[P] Ω[P⁄R] ≃ₗ[K] (Fin n → K),
      ∀ a : MvPolynomial (Fin n) R,
        e ((1 : K) ⊗ₜ[P] KaehlerDifferential.D R P (algebraMap (MvPolynomial (Fin n) R) P a)) =
          fun i => algebraMap (MvPolynomial (Fin n) R) K (MvPolynomial.pderiv i a) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization.solution
