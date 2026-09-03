import Mathlib
import P2M.Util
import P2M.Sol.S_Pencil_exists_rootOfUnity_torus_covector_sum_log_ge
attribute [-simp] MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox

theorem Pencil.exists_rootOfUnity_torus_covector_sum_log_ge {r : ℕ} (v : Fin r → ℂ) {i₀ : Fin r}
    (hi₀ : ∀ i, ‖v i‖ ≤ ‖v i₀‖)
    {ι : Type*} (T : Finset ι) (w : ι → Fin r → ℂ) (n : ι → ℕ)
    (hw : ∀ t ∈ T, ∃ p : Fin r × Fin r, v p.1 * w t p.2 - v p.2 * w t p.1 ≠ 0) :
    ∃ z : Fin r → ℂ, (∀ j, ∃ m : ℕ, 0 < m ∧ z j ^ m = 1) ∧
      ∑ t ∈ T, (n t : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖v p.1 * w t p.2 - v p.2 * w t p.1‖)
          - (∑ t ∈ T, (n t : ℝ)) * (r * Real.log 2 + 1)
        ≤ ∑ t ∈ T, (n t : ℝ) * Real.log ‖∑ j, z j * (v i₀ * w t j - v j * w t i₀)‖ := by p2m_exact_reverting @_root_.P2MW.S_Pencil_exists_rootOfUnity_torus_covector_sum_log_ge.solution
