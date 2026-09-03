import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization

set_option autoImplicit false

open MvPolynomial TensorProduct KaehlerDifferential

theorem MvPolynomial.formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P] :
    Algebra.FormallySmooth R P ∧ Module.Free P Ω[P⁄R] ∧ Module.Finite P Ω[P⁄R] := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization.solution
