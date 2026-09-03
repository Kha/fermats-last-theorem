import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay

open Set MeasureTheory
set_option autoImplicit false

theorem AutomorphicForm.ComplexIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay (a b : ℕ) :
    let j : ℂ → ℂ → ℂ := fun w ζ => ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w : ℂ) (ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 → J w ζ = j w ζ) ∧
      ContinuousOn (fun p : ℂ × ℂ => J p.1 p.2) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) ∧
      (∀ K : Set ℂ, IsCompact K → ∃ M : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖J w ζ‖ ≤ C * ‖ζ‖ ^ (-(M : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay.solution
