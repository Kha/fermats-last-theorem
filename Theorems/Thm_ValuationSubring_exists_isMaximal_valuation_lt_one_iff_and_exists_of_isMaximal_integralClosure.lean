import Mathlib.RingTheory.Valuation.ValuationSubring
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure

theorem ValuationSubring.exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    (O : ValuationSubring E) :
    (∀ O' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) →
      ∃ M : Ideal (integralClosure O F), M.IsMaximal ∧
        ∀ b : integralClosure O F, O'.valuation (b : F) ≤ 1 ∧ (O'.valuation (b : F) < 1 ↔ b ∈ M)) ∧
    (∀ M : Ideal (integralClosure O F), M.IsMaximal →
      ∃ O' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) ∧
        ∀ b : integralClosure O F, O'.valuation (b : F) ≤ 1 ∧ (O'.valuation (b : F) < 1 ↔ b ∈ M)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure.solution
