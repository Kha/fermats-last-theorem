import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one
    {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ] [μ.IsNegInvariant]
    (n : X → G) (hn : Measurable n) (hn_add : ∀ x y, n (x + y) = n x * n y)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦn : ∀ g x, Φ (g * n x) = Φ g)
    (w w₀ : G → ℝ≥0∞) (hw : Measurable w) (hw₀ : Measurable w₀)
    (h1 : ∀ᵐ g ∂τ, ∫⁻ x, w (g * n x) ∂μ = 1) (h1₀ : ∀ᵐ g ∂τ, ∫⁻ x, w₀ (g * n x) ∂μ = 1) :
    ∫⁻ g, w g * Φ g ∂τ = ∫⁻ g, w₀ g * Φ g ∂τ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one.solution
