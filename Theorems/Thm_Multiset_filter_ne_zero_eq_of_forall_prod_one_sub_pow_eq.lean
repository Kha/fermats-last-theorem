import Mathlib
import P2M.Util
import P2M.Sol.S_Multiset_filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq

set_option autoImplicit false

theorem Multiset.filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq
    (s t : Multiset ℂ) (c : ℝ) (hc : 1 < c) (ht : ∀ z ∈ t, ‖z‖ = c)
    (h : ∀ n : ℕ, 0 < n →
      (s.map fun z => 1 - z ^ n).prod = (t.map fun z => 1 - z ^ n).prod) :
    s.filter (fun z => z ≠ 0) = t := by p2m_exact_reverting @_root_.P2MW.S_Multiset_filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq.solution
