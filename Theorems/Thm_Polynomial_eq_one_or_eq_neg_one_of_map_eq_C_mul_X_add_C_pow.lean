import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow

set_option autoImplicit false

open Polynomial

theorem Polynomial.eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow
    (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ) (hg : 1 ≤ g) (P : ℚ[X]) (a : ℚ) (ha : a = 1 ∨ a = -1)
    (h0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1) (r : ℚ_[ℓ])
    (hP : P.map (algebraMap ℚ ℚ_[ℓ]) = C (algebraMap ℚ ℚ_[ℓ] a) * (X + C r) ^ g) :
    r = 1 ∨ r = -1 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow.solution
