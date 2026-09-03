import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero
    (a d : ℕ) (Y : Type) [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (vol : Measure Y) (m : Measure (Fin d → AddCircle (1 : ℝ))) [IsProbabilityMeasure m]
    (n₀ : Fin d → ℤ) (P : (Fin a → ℤ) → Y → (Fin d → AddCircle (1 : ℝ))) (hP : ∀ κ, Continuous (P κ))
    (c : (Fin a → ℤ) → Y → ℂ) (hcc : ∀ κ, Continuous (c κ)) (hci : ∀ κ, Integrable (c κ) vol)
    (hcs : Summable fun κ => ∫ y, ‖c κ y‖ ∂vol)
    (hfib : ∀ (τ : Fin d → AddCircle (1 : ℝ)) (κ : Fin a → ℤ),
      ∀ᵐ y ∂vol, m {q : Fin d → AddCircle (1 : ℝ) | P κ y + q = τ} = 0) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      ‖μ‖ ≤ ∑' κ, ∫ y, ‖c κ y‖ ∂vol ∧
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) →
        μ e = ∑' κ, ∫ y, c κ y * ((∏ i, fourier (n i - n₀ i) (P κ y i)) *
          ∫ q, ∏ i, fourier (n i - n₀ i) (q i) ∂m) ∂vol := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero.solution
