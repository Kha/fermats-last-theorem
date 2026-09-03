import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_Raynaud_valProfile_eq_zero_of_ramification_lt

theorem HopfAlgebra.Raynaud.valProfile_eq_zero_of_ramification_lt
    {r p e : ℕ} (hpe : e + 1 < p)
    {n n' : Fin (r + 1) → ℕ} {a : Fin (r + 1) → ℤ}
    (hprof : ∀ i : Fin (r + 1), (n' i : ℤ) = p * a i + (n i : ℤ) - a (i + 1))
    (hpos : ∀ i, 0 ≤ a i) (hbound : ∀ i, n' i ≤ e) :
    ∀ i, a i = 0 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_Raynaud_valProfile_eq_zero_of_ramification_lt.solution
