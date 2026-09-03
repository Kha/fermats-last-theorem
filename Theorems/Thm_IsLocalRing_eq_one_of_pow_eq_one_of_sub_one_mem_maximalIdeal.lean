import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal

set_option autoImplicit false

universe u v

open IsLocalRing
theorem IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A]
    {u : A} (hu : u - 1 ∈ IsLocalRing.maximalIdeal A) {n : ℕ} (hn : IsUnit (n : A)) (hun : u ^ n = 1) : u = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal.solution
