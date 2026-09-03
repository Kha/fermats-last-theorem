import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (m : ↥A) (hm : m ∈ maximalIdeal ↥A) (hm0 : (m : L) ≠ 0) :
    ∃ c₁ c₂ : ↥A, c₁ ∈ maximalIdeal ↥A ∧ c₂ ∈ maximalIdeal ↥A ∧ (c₁ : L) ≠ 0 ∧ (c₂ : L) ≠ 0 ∧
      (∃ m₁ ∈ maximalIdeal ↥A, (m : L) = c₁ * m₁) ∧ (∃ m₂ ∈ maximalIdeal ↥A, (m : L) = c₂ * m₂) ∧
      A.valuation (c₁ : L) ≠ A.valuation (c₂ : L) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed.solution
