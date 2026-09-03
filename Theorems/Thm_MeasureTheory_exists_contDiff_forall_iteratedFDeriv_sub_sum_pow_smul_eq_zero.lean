import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero

set_option autoImplicit false

theorem MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (C : Set E) (hC : IsCompact C)
    (a : ℕ → E → F) (ha : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) (hsupp : ∀ k (e : E), e ∉ C → a k e = 0) :
    ∃ B : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (n m : ℕ), m ≤ n → ∀ e : E,
        iteratedFDeriv ℝ m
          (fun p : E × ℝ => B p - ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1) (e, 0) = 0 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero.solution
