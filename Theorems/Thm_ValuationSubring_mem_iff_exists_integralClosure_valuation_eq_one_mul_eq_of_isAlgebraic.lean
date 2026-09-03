import Mathlib.RingTheory.Valuation.ValuationSubring
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic

theorem ValuationSubring.mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [Algebra.IsAlgebraic E F]
    (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) :
    (∀ x : F, x ∈ O' ↔ ∃ b s : integralClosure O F, O'.valuation (s : F) = 1 ∧ x * s = b) ∧
    (∀ O'' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) →
      (∀ b : integralClosure O F, O'.valuation (b : F) < 1 ↔ O''.valuation (b : F) < 1) → O'' = O') := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_iff_exists_integralClosure_valuation_eq_one_mul_eq_of_isAlgebraic.solution
