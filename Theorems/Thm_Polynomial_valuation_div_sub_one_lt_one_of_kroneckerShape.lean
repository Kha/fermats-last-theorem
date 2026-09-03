import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_valuation_div_sub_one_lt_one_of_kroneckerShape

set_option autoImplicit false

open Polynomial
theorem Polynomial.valuation_div_sub_one_lt_one_of_kroneckerShape
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : K[X]) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (y : K) (hy : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).IsRoot y) :
    v (y / x₀ ^ q - 1) < 1 ∨ (1 < v y ∧ v (x₀ / y ^ q - 1) < 1) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_valuation_div_sub_one_lt_one_of_kroneckerShape.solution
