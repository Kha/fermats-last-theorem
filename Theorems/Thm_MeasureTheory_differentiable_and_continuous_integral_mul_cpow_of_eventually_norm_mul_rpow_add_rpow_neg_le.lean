import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le

set_option autoImplicit false

theorem MeasureTheory.differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le
    {X : Type*} [MeasurableSpace X] (m : MeasureTheory.Measure X)
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (N : X → ℝ) (hN : AEMeasurable N m) (hNpos : ∀ x, 0 < N x)
    (h : P → X → ℂ) (hh : ∀ p, MeasureTheory.AEStronglyMeasurable (h p) m)
    (hcont : ∀ᵐ x ∂m, Continuous fun p => h p x)
    (hdom : ∀ (p₀ : P) (M : ℝ), ∃ bound : X → ℝ, MeasureTheory.Integrable bound m ∧
      ∀ᶠ p in nhds p₀, ∀ᵐ x ∂m, ‖h p x‖ * (N x ^ M + N x ^ (-M)) ≤ bound x) :
    (∀ p : P, Differentiable ℂ fun s : ℂ => ∫ x, h p x * ((N x : ℝ) : ℂ) ^ s ∂m) ∧
    (Continuous fun q : ℂ × P => ∫ x, h q.2 x * ((N x : ℝ) : ℂ) ^ q.1 ∂m) ∧
    (∀ (p : P) (M : ℝ) (s : ℂ), |s.re| ≤ M →
      MeasureTheory.Integrable (fun x => ‖h p x‖ * (N x ^ M + N x ^ (-M))) m ∧
      ‖∫ x, h p x * ((N x : ℝ) : ℂ) ^ s ∂m‖ ≤ ∫ x, ‖h p x‖ * (N x ^ M + N x ^ (-M)) ∂m) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le.solution
