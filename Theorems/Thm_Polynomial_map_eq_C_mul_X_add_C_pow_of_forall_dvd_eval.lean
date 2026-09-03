import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval

set_option autoImplicit false

open Polynomial

theorem Polynomial.map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval
    (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ) (P : ℚ[X]) (hdeg : P.natDegree ≤ g)
    (χ : ℕ → ℤ) (hχ : ∀ m : ℕ, P.eval (m : ℚ) = (χ m : ℚ)) (c : ℤ_[ℓ])
    (hval : ∀ m : ℕ, (m : ℤ_[ℓ]) + c ≠ 0 → ((m : ℤ_[ℓ]) + c) ^ g ∣ (χ m : ℤ_[ℓ])) :
    P.map (algebraMap ℚ ℚ_[ℓ]) =
      C (algebraMap ℚ ℚ_[ℓ] (P.coeff g)) * (X + C (c : ℚ_[ℓ])) ^ g := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_map_eq_C_mul_X_add_C_pow_of_forall_dvd_eval.solution
