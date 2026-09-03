import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span

open PowerSeries

theorem PowerSeries.mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span
    {A : Type*} [CommRing A] [IsLocalRing A] (n : ℕ) (hn : IsUnit (n : A))
    (u : PowerSeries A) (hu : IsUnit (constantCoeff u))
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (π : A)
    (h : ∀ k < n, coeff k (u * (X - C a) ^ n - X ^ n) ∈ Ideal.span {π}) :
    a ∈ Ideal.span {π} ∧
      ∀ k, k + 2 ≤ n → coeff k (u * (X - C a) ^ n - X ^ n) ∈ Ideal.span {π * a} := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span.solution
