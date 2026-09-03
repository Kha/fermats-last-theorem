import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Basic
import P2M.Util
import P2M.Sol.S_Complex_exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero

theorem Complex.exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero
    {ι : Type} (t : Finset ι) (f : ι → ℂ → ℂ) (σ : ℝ)
    (hf : ∀ i ∈ t, DifferentiableOn ℂ (f i) {s : ℂ | σ < s.re})
    (hne : ∀ i ∈ t, ∃ s : ℂ, σ < s.re ∧ f i s ≠ 0)
    (σ' : ℝ) :
    ∃ s : ℂ, σ' < s.re ∧ σ < s.re ∧ ∀ i ∈ t, f i s ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero.solution
