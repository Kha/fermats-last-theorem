import Mathlib
import P2M.Util
import P2M.Sol.S_LocalParametrix_exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top

set_option autoImplicit false

open MeasureTheory Topology

theorem LocalParametrix.exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] (A : ι → E →L[ℝ] E) (x₀ : E)
    (hA : Submodule.span ℝ (Set.range fun i => A i x₀) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ E < 2 * m) (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, ((fun (G : E → ℂ) (y : E) =>
                  ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => A i y))^[m] F) x * g₁ x ∂μ) +
          ∫ x, F x * g₂ x ∂μ := by p2m_exact_reverting @_root_.P2MW.S_LocalParametrix_exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top.solution
