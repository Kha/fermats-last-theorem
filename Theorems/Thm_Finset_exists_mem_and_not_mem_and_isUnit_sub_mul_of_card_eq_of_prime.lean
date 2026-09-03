import Mathlib
import P2M.Util
import P2M.Sol.S_Finset_exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime

set_option autoImplicit false

theorem Finset.exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime
    (q : ℕ) [Fact q.Prime] (S : Finset (ℕ × ℕ)) (hS : S ⊆ Finset.range q ×ˢ Finset.range q)
    (hcard : S.card = q) :
    ∃ a b c d : ℕ, (a, b) ∈ S ∧ c < q ∧ d < q ∧ (c, d) ∉ S ∧
      IsUnit (((a * d : ℤ) - (b * c : ℤ) : ℤ) : ZMod q) := by p2m_exact_reverting @_root_.P2MW.S_Finset_exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime.solution
