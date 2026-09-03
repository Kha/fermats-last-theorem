import Mathlib
import P2M.Util
import P2M.Sol.S_Valuation_map_eval_eq_pow_of_one_lt

theorem Valuation.map_eval_eq_pow_of_one_lt {R : Type*} [CommRing R]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    {f : Polynomial R} {x : R} (hc : ∀ i, v (f.coeff i) ≤ 1) (hl : v f.leadingCoeff = 1)
    (hx : 1 < v x) : v (f.eval x) = v x ^ f.natDegree := by p2m_exact_reverting @_root_.P2MW.S_Valuation_map_eval_eq_pow_of_one_lt.solution
