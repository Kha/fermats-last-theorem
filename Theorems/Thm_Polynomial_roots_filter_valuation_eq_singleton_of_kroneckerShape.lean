import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_roots_filter_valuation_eq_singleton_of_kroneckerShape

theorem Polynomial.roots_filter_valuation_eq_singleton_of_kroneckerShape
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : Polynomial K) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (hsplit : ((Polynomial.C (x₀ ^ q) - Polynomial.X) * (Polynomial.C x₀ - Polynomial.X ^ q)
      + Polynomial.C c * H).Splits) :
    ∃ y₀ : K, (((Polynomial.C (x₀ ^ q) - Polynomial.X) * (Polynomial.C x₀ - Polynomial.X ^ q)
        + Polynomial.C c * H).roots.filter fun y => v y = v x₀ ^ q) = {y₀} := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_roots_filter_valuation_eq_singleton_of_kroneckerShape.solution
