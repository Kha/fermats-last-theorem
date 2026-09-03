import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq
    {X T₁ T₂ : Type*} [MeasurableSpace X] [MeasurableSpace T₁] [MeasurableSpace T₂]
    (m : Measure X) (μ₁ : Measure T₁) (μ₂ : Measure T₂) [SFinite m] [SFinite μ₁] [SFinite μ₂]
    (E₁ : X × T₁ → ℤ) (hE₁ : Measurable E₁) (E₂ : X × T₂ → ℤ) (hE₂ : Measurable E₂)
    (G₁ : X × T₁ → ℂ) (G₂ : X × T₂ → ℂ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hG₁ : ∀ r : ℝ, a₁ < r → r < b₁ → Integrable (fun p => G₁ p * (r : ℂ) ^ E₁ p) (m.prod μ₁))
    (hG₂ : ∀ r : ℝ, a₂ < r → r < b₂ → Integrable (fun p => G₂ p * (r : ℂ) ^ E₂ p) (m.prod μ₂))
    (Q₁ Q₂ : Polynomial ℂ) (C : ℂ) (k : ℤ)
    (hfe : ∀ᵐ x ∂m, ∃ (P : Polynomial ℂ) (n : ℤ) (a₁' b₁' a₂' b₂' : ℝ),
      0 ≤ a₁' ∧ a₁' < b₁' ∧ 0 ≤ a₂' ∧ a₂' < b₂' ∧
      (∀ Y : ℂ, a₁' < ‖Y‖ → ‖Y‖ < b₁' →
        Integrable (fun t => G₁ (x, t) * Y ^ E₁ (x, t)) μ₁ ∧
        (∫ t, G₁ (x, t) * Y ^ E₁ (x, t) ∂μ₁) * Q₁.eval Y = P.eval Y * Y ^ n) ∧
      (∀ Y : ℂ, a₂' < ‖Y‖ → ‖Y‖ < b₂' →
        Integrable (fun t => G₂ (x, t) * Y ^ E₂ (x, t)) μ₂ ∧
        (∫ t, G₂ (x, t) * Y ^ E₂ (x, t) ∂μ₂) * Q₂.eval Y = C * Y ^ k * (P.eval Y * Y ^ n))) :
    ∃ e : ℤ → ℂ,
      (∀ r : ℝ, a₁ < r → r < b₁ → Summable fun j : ℤ => ‖e j‖ * r ^ j) ∧
      (∀ Y : ℂ, a₁ < ‖Y‖ → ‖Y‖ < b₁ →
        HasSum (fun j : ℤ => e j * Y ^ j) (Q₁.eval Y * ∫ p, G₁ p * Y ^ E₁ p ∂(m.prod μ₁))) ∧
      (∀ r : ℝ, a₂ < r → r < b₂ → Summable fun j : ℤ => ‖C * e (j - k)‖ * r ^ j) ∧
      (∀ Y : ℂ, a₂ < ‖Y‖ → ‖Y‖ < b₂ →
        HasSum (fun j : ℤ => C * e (j - k) * Y ^ j) (Q₂.eval Y * ∫ p, G₂ p * Y ^ E₂ p ∂(m.prod μ₂))) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq.solution
