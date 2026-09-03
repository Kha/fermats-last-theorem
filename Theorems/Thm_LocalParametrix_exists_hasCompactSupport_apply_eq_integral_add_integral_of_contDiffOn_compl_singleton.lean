import Mathlib
import P2M.Util
import P2M.Sol.S_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton

set_option autoImplicit false

open MeasureTheory Topology

theorem LocalParametrix.exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (D : (E → ℂ) → (E → ℂ))
    (hD_add : ∀ F G : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G → D (F + G) = D F + D G)
    (hD_cont : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → Continuous (D F))
    (hD_supp : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport (D F) ⊆ tsupport F)
    (hD_tr : ∀ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∃ h : E → ℂ, Continuous h ∧ tsupport h ⊆ tsupport g ∧
        ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
          ∫ x, D F x * g x ∂μ = ∫ x, F x * h x ∂μ)
    (x₀ : E) (u w : E → ℂ) (hu : Continuous u) (hw : Continuous w)
    (hu' : ContDiffOn ℝ (⊤ : ℕ∞) u {x₀}ᶜ)
    (hid : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      F x₀ = (∫ x, D F x * u x ∂μ) + ∫ x, F x * w x ∂μ)
    (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ := by p2m_exact_reverting @_root_.P2MW.S_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton.solution
