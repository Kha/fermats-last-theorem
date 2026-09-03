import Mathlib
import P2M.Util
import P2M.Sol.S_contDiff_top_and_hasCompactSupport_integral_comp_affine

set_option autoImplicit false

open MeasureTheory

theorem contDiff_top_and_hasCompactSupport_integral_comp_affine
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (Ψ : F → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ)
    {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (K : Set P) (hK : IsCompact K) (hμK : μ Kᶜ = 0)
    (c : P → ℂ) (hc : Continuous c)
    (A : P → (E →L[ℝ] F)) (hA : Continuous A) (b : P → F) (hb : Continuous b)
    (C : ℝ) (hproper : ∀ p ∈ K, ∀ e : E, ‖e‖ ≤ C * (‖A p e‖ + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun e : E => ∫ p, c p * Ψ (A p e + b p) ∂μ) ∧
      HasCompactSupport (fun e : E => ∫ p, c p * Ψ (A p e + b p) ∂μ) := by p2m_exact_reverting @_root_.P2MW.S_contDiff_top_and_hasCompactSupport_integral_comp_affine.solution
