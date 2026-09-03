import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm

set_option autoImplicit false

open Polynomial

theorem Polynomial.exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm
    (R : Type*) [CommRing R] (A : Type*) [Field A] [Algebra R A]
    (n : ℕ) (P : Polynomial (Polynomial R)) (hmon : P.Monic) (hdeg : P.natDegree = n + 1)
    (hsym : ∀ i j, (P.coeff i).coeff j = (P.coeff j).coeff i) :
    ∃ h : Polynomial R,
      ∀ (x y c : A), x ≠ 0 → y ≠ 0 →
        P.eval₂ (Polynomial.eval₂RingHom (algebraMap R A) x) y = 0 →
        c * (1 + x⁻¹ * Polynomial.aeval x⁻¹ h) = 1 →
        IsIntegral (Algebra.adjoin R ({x⁻¹, c} : Set A)) y⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm.solution
