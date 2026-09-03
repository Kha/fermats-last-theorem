import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {β : Type} [NormedAddCommGroup β] [NormedSpace ℝ β] [FiniteDimensional ℝ β]
    [MeasurableSpace β] [BorelSpace β]
    {α : Type} [MeasurableSpace α] (μ : Measure α)
    (G : E × β → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    (π : α → β) (hπ : Measurable π)
    (h : α → ℂ) (hh : AEStronglyMeasurable h μ)
    (A : Set α) (hA : MeasurableSet A) (hμA : μ A < ⊤)
    (C : ℝ) (hhA : ∀ a ∈ A, ‖h a‖ ≤ C) (hh0 : ∀ a, a ∉ A → h a = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => ∫ a, h a * G (x, π a) ∂μ) ∧
    HasCompactSupport (fun x : E => ∫ a, h a * G (x, π a) ∂μ) ∧
    ∀ x : E, x ∉ Prod.fst '' tsupport G → (∫ a, h a * G (x, π a) ∂μ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport.solution
