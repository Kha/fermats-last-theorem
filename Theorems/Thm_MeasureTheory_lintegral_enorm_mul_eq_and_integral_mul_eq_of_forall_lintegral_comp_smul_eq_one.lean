import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one
    {A X : Type*} [Group A] [MulAction A X] [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
    (hact : Measurable fun z : A × X => z.1 • z.2)
    (τ : Measure A) [SFinite τ] [τ.IsInvInvariant]
    (ρ : Measure X) [SFinite ρ] (hρ : ∀ a : A, MeasurePreserving (fun x : X => a • x) ρ ρ)
    (h : X → ℂ) (hh : Measurable h) (hhA : ∀ (a : A) (x : X), h (a • x) = h x)
    (w₁ w₂ : X → ℝ) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (hs₁ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (hs₂ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₁ x) ∂ρ = ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₂ x) ∂ρ ∧
      (Integrable (fun x => h x * (w₁ x : ℂ)) ρ →
        Integrable (fun x => h x * (w₂ x : ℂ)) ρ ∧
          ∫ x, h x * (w₁ x : ℂ) ∂ρ = ∫ x, h x * (w₂ x : ℂ) ∂ρ) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one.solution
