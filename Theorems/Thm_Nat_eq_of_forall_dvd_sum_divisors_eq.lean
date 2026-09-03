import Mathlib
import P2M.Util
import P2M.Sol.S_Nat_eq_of_forall_dvd_sum_divisors_eq

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum
theorem Nat.eq_of_forall_dvd_sum_divisors_eq {n : ℕ} (hn : 0 < n) (m m' : ℕ → ℕ)
    (h : ∀ e, e ∣ n → ∑ d ∈ e.divisors, m d = ∑ d ∈ e.divisors, m' d) :
    ∀ d, d ∣ n → m d = m' d := by p2m_exact_reverting @_root_.P2MW.S_Nat_eq_of_forall_dvd_sum_divisors_eq.solution
