import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hcont : ∀ f ∈ V, Continuous f)
    (hinv : ∀ f ∈ V, ∀ g : G, (fun x => f (x * g)) ∈ V) :
    ∀ f ∈ V, ∀ x : G,
      ‖f x‖ ^ 2 * μ.real Set.univ ≤ (Module.finrank ℂ V : ℝ) * ∫ y, ‖f y‖ ^ 2 ∂μ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem.solution
