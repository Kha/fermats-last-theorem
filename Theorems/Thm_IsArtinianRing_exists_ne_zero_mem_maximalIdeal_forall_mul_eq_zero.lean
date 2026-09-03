import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero

set_option autoImplicit false

theorem IsArtinianRing.exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero
    (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (h : IsLocalRing.maximalIdeal B ≠ ⊥) :
    ∃ t : B, t ≠ 0 ∧ t ∈ IsLocalRing.maximalIdeal B ∧ ∀ m ∈ IsLocalRing.maximalIdeal B, m * t = 0 := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero.solution
