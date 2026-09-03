import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing

theorem ValuationSubring.forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (O : ValuationSubring K) [HenselianLocalRing O]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) :
    (∀ x : L, x ∈ V ↔ IsIntegral O x) ∧
      ∀ V' : ValuationSubring L, (∀ x : K, algebraMap K L x ∈ V' ↔ x ∈ O) → V' = V := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing.solution
