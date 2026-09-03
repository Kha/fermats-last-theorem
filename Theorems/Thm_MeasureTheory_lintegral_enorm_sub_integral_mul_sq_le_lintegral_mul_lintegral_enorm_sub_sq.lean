import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (ν : Measure X) (ρ : Measure A) [SFinite ν] [SFinite ρ]
    (p : A → ℝ) (hp : Measurable p) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∫ a, p a ∂ρ = 1)
    (u : X → ℂ) (hu : Measurable u) (U : X → A → ℂ) (hU : Measurable (Function.uncurry U))
    (hint : ∀ x, Integrable (fun a => U x a * (p a : ℂ)) ρ) :
    ∫⁻ x, ‖u x - ∫ a, U x a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ x, ‖u x - U x a‖ₑ ^ 2 ∂ν ∂ρ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq.solution
