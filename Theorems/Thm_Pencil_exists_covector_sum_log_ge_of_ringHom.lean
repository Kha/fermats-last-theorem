import Mathlib
import P2M.Util
import P2M.Sol.S_Pencil_exists_covector_sum_log_ge_of_ringHom
attribute [-simp] MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox

theorem Pencil.exists_covector_sum_log_ge_of_ringHom {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {r : ℕ} (v : Fin r → F) {i₀ : Fin r}
    (hi₀ : ∀ i, ‖σ (v i)‖ ≤ ‖σ (v i₀)‖)
    {ι : Type*} (T : Finset ι) (w : ι → Fin r → ℂ) (n : ι → ℕ)
    (hw : ∀ t ∈ T, ∃ p : Fin r × Fin r, σ (v p.1) * w t p.2 - σ (v p.2) * w t p.1 ≠ 0) :
    ∃ a : Fin r → F, (∑ i, v i * a i = 0) ∧
      (∀ i, ‖σ (a i)‖ ≤ r * ‖σ (v i₀)‖) ∧ (∀ i, i ≠ i₀ → ‖σ (a i)‖ = ‖σ (v i₀)‖) ∧
      ∑ t ∈ T, (n t : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖σ (v p.1) * w t p.2 - σ (v p.2) * w t p.1‖)
          - (∑ t ∈ T, (n t : ℝ)) * (r * Real.log 2 + 1)
        ≤ ∑ t ∈ T, (n t : ℝ) * Real.log ‖∑ i, σ (a i) * w t i‖ := by p2m_exact_reverting @_root_.P2MW.S_Pencil_exists_covector_sum_log_ge_of_ringHom.solution
