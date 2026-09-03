import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic
import P2M.Util
import P2M.Sol.S_MeasureTheory_integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm
    {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] [Countable ι]
    (H : ι → X × Y → ℂ) (hH : ∀ i, Integrable (H i) (μ.prod ν))
    (hS : Summable fun i => ∫ p, ‖H i p‖ ∂(μ.prod ν)) :
    (∀ i, Integrable (fun x => ∫ y, H i (x, y) ∂ν) μ) ∧
    (∀ i, Integrable (fun y => ∫ x, H i (x, y) ∂μ) ν) ∧
    (Summable fun i => ∫ x, ‖∫ y, H i (x, y) ∂ν‖ ∂μ) ∧
    (Summable fun i => ∫ y, ‖∫ x, H i (x, y) ∂μ‖ ∂ν) ∧
    Integrable (fun y => ∑' i, ∫ x, H i (x, y) ∂μ) ν ∧
    ∫ y, ∑' i, ∫ x, H i (x, y) ∂μ ∂ν = ∑' i, ∫ x, ∫ y, H i (x, y) ∂ν ∂μ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm.solution
