import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_mem_of_mul_eval2_mem_of_forall_coeff_mem_maximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem AlgebraicCurve.mem_of_mul_eval2_mem_of_forall_coeff_mem_maximalIdeal
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] (S : Subring F)
    (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S) (T : F) (hT : T ∈ S) (f : F)
    (P : Polynomial ↥A) (hP : P.Monic) (hPc : ∀ i : ℕ, i < P.natDegree → P.coeff i ∈ maximalIdeal ↥A)
    (hfP : f * Polynomial.eval₂ ((algebraMap L F).comp (algebraMap ↥A L)) T P ∈ S)
    (hc : ∀ c : ↥A, c ∈ maximalIdeal ↥A →
      ∃ O : Subring F, S ≤ O ∧ f ∈ O ∧ ∀ u : F, u ∈ O → u * (T - algebraMap L F (c : L)) ∈ S → u ∈ S) :
    f ∈ S := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_mem_of_mul_eval2_mem_of_forall_coeff_mem_maximalIdeal.solution
