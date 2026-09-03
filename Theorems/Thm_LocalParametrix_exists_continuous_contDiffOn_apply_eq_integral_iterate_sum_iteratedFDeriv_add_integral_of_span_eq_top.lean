import Mathlib
import P2M.Util
import P2M.Sol.S_LocalParametrix_exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top

set_option autoImplicit false

open MeasureTheory Topology

theorem LocalParametrix.exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {ι : Type*} [Fintype ι] (A : ι → V →L[ℝ] V) (x₀ : V)
    (hA : Submodule.span ℝ (Set.range fun i => A i x₀) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ V < 2 * m) :
    ∃ u w : V → ℂ, Continuous u ∧ Continuous w ∧ ContDiffOn ℝ (⊤ : ℕ∞) u {x₀}ᶜ ∧
      ∀ F : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, ((fun (G : V → ℂ) (y : V) =>
                  ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => A i y))^[m] F) x * u x) +
          ∫ x, F x * w x := by p2m_exact_reverting @_root_.P2MW.S_LocalParametrix_exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top.solution
