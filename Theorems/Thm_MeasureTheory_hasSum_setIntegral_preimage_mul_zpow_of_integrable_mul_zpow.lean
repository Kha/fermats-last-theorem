import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) (E : Ω → ℤ) (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, ‖G ω‖ ∂ρ) * r ^ n) (∫ ω, ‖G ω‖ * r ^ E ω ∂ρ) ∧
    (Summable fun n : ℤ => ‖∫ ω in E ⁻¹' {n}, G ω ∂ρ‖ * r ^ n) ∧
    ∀ Y : ℂ, ‖Y‖ = r →
      Integrable (fun ω => G ω * Y ^ E ω) ρ ∧
      HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, G ω ∂ρ) * Y ^ n) (∫ ω, G ω * Y ^ E ω ∂ρ) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow.solution
