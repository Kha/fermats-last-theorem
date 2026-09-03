import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import P2M.Util
import P2M.Sol.S_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφmax : ∀ v, φ v ≤ φ 0)
    (γ δ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (hout : ∀ v, δ < |v| → φ v ≤ φ 0 - γ) (hin : ∀ v, |v| ≤ ρ → φ 0 - γ / 2 ≤ φ v)
    (H : ℝ → ℝ) (Λ₀ : ℝ) (hΛ₀ : 0 ≤ Λ₀)
    (hHint : Integrable (fun v => Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v))
    (hHloc : IntegrableOn H {v | |v| ≤ δ})
    (h : ℝ → ℝ) (hhm : Measurable h) (hh0 : ∀ v, 0 ≤ h v) (hhH : ∀ v, h v ≤ H v)
    (cm : ℝ) (hhin : ∀ v, |v| ≤ ρ → Real.exp cm ≤ h v)
    (Λ : ℝ) (hΛ : Λ₀ ≤ Λ) :
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | δ < |v|} ∧
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | |v| ≤ δ} ∧
    ∫ v in {v | δ < |v|}, Real.exp (Λ * φ v) * h v ≤
      ((∫ v, Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v) * Real.exp (-cm) / (2 * ρ)) * Real.exp (-(Λ * γ / 2)) *
        ∫ v in {v | |v| ≤ δ}, Real.exp (Λ * φ v) * h v := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap.solution
