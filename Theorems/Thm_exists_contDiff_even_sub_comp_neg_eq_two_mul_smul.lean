import Mathlib
import P2M.Util
import P2M.Sol.S_exists_contDiff_even_sub_comp_neg_eq_two_mul_smul

set_option autoImplicit false

theorem exists_contDiff_even_sub_comp_neg_eq_two_mul_smul
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (B : E × ℝ → F) (hB : ContDiff ℝ (⊤ : ℕ∞) B) :
    ∃ Q : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) Q ∧ (∀ (e : E) (ρ : ℝ), Q (e, -ρ) = Q (e, ρ)) ∧
      ∀ (e : E) (ρ : ℝ), B (e, ρ) - B (e, -ρ) = (2 * ρ) • Q (e, ρ) := by p2m_exact_reverting @_root_.P2MW.S_exists_contDiff_even_sub_comp_neg_eq_two_mul_smul.solution
