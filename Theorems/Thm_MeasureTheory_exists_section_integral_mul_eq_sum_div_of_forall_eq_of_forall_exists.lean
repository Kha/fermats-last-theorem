import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : Set G)
    (hUo : IsOpen U) (hUc : IsCompact U) (hμUtop : μ U ≠ ⊤)
    (h1U : (1 : G) ∈ U) (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) (hUinv : ∀ a ∈ U, a⁻¹ ∈ U)
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts τ] [τ.IsOpenPosMeasure]
    (ψ : G → ℂ) (hψ : ∀ t ∈ T, ∀ x : G, ∀ u ∈ U, ψ (t * x * u) = ψ x)
    (S : Finset G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s)
    (hcov : ∀ x, ψ x ≠ 0 → ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      (∀ x, ψ x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∫ x, ψ x * (w x : ℂ) ∂μ =
        ∑ s ∈ S, ψ s * ((μ U).toReal : ℂ) / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists.solution
