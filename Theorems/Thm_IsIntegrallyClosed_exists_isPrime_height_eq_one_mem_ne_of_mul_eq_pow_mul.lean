import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul
set_option autoImplicit false

theorem IsIntegrallyClosed.exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul
    {D : Type*} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]
    (ϖ : D) (hϖ : ϖ ≠ 0)
    (Q₁ : Ideal D) [Q₁.IsPrime]
    (G H u : D) (e : ℕ) (hH : ¬ IsUnit H) (hHQ₁ : H ∉ Q₁)
    (hu : IsUnit u) (hGH : G * H = ϖ ^ e * u) :
    ∃ Q : Ideal D, Q.IsPrime ∧ Q.height = 1 ∧ ϖ ∈ Q ∧ Q ≠ Q₁ := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul.solution
