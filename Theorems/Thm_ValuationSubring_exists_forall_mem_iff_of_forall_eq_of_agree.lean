import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_mem_iff_of_forall_eq_of_agree

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_forall_mem_iff_of_forall_eq_of_agree
    {K₁ K T F : Type*} [Field K₁] [Field K] [Field T] [Field F]
    [Algebra K₁ K] [Algebra K₁ T] [Algebra K F] [Algebra T F] [Algebra K₁ F]
    [IsScalarTower K₁ K F] [IsScalarTower K₁ T F]
    (A : ValuationSubring K) (V : ValuationSubring T)
    (hagree : ∀ x : K₁, algebraMap K₁ K x ∈ A ↔ algebraMap K₁ T x ∈ V)
    (hU : ∀ A' : ValuationSubring K, (∀ x : K₁, algebraMap K₁ K x ∈ A' ↔ algebraMap K₁ K x ∈ A) → A' = A) :
    ∃ O : ValuationSubring F,
      (∀ t : T, algebraMap T F t ∈ O ↔ t ∈ V) ∧ (∀ k : K, algebraMap K F k ∈ O ↔ k ∈ A) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_mem_iff_of_forall_eq_of_agree.solution
