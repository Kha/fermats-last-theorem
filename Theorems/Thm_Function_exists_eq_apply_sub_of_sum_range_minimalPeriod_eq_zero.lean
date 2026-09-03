import Mathlib
import P2M.Util
import P2M.Sol.S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero

set_option autoImplicit false

theorem Function.exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero {X : Type*} {A : Type*} [AddCommGroup A]
    (f : X → X) (hf : ∀ x : X, 0 < Function.minimalPeriod f x) (v : X → A)
    (hv : ∀ x : X, ∑ k ∈ Finset.range (Function.minimalPeriod f x), v (f^[k] x) = 0) :
    ∃ G : X → A, ∀ x : X, v x = G (f x) - G x := by p2m_exact_reverting @_root_.P2MW.S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero.solution
