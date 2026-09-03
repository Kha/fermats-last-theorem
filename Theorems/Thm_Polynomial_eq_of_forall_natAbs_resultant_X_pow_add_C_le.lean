import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_eq_of_forall_natAbs_resultant_X_pow_add_C_le

set_option autoImplicit false

theorem Polynomial.eq_of_forall_natAbs_resultant_X_pow_add_C_le (P Q : Polynomial ℤ)
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ n : ℕ, 0 < n → ∀ c ∈ S,
      (Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant P ≠ 0 →
        ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant Q).natAbs ≤
          ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant P).natAbs) :
    P = Q := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_eq_of_forall_natAbs_resultant_X_pow_add_C_le.solution
