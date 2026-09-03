import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero

set_option autoImplicit false

theorem MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : E × ℝ → F) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {p : E × ℝ | 0 ≤ p.2})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → Ψ p = 0) :
    ∃ a : ℕ → E → F, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) ∧ (∀ k (e : E), e ∉ C → a k e = 0) ∧
      ∀ (n m : ℕ), m ≤ n → ∀ e : E,
        iteratedFDerivWithin ℝ m
          (fun p : E × ℝ => Ψ p - ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1)
          {p : E × ℝ | 0 ≤ p.2} (e, 0) = 0 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero.solution
