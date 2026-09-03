import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup

theorem ValuationSubring.isAlgClosed_completion_of_mulArchimedean_valueGroup
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (A : ValuationSubring K) [MulArchimedean A.ValueGroup] (hA : A ≠ ⊤) :
    IsAlgClosed A.valuation.Completion := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup.solution
