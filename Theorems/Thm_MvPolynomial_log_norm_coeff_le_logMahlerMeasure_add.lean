import Definitions.Def_MvPolynomial_LogMahlerMeasure
import P2M.Util
import P2M.Sol.S_MvPolynomial_log_norm_coeff_le_logMahlerMeasure_add

theorem MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add {n : ℕ} (P : MvPolynomial (Fin n) ℂ) {m : Fin n →₀ ℕ} (hm : m ∈ P.support) :
    Real.log ‖MvPolynomial.coeff m P‖ ≤
      P.logMahlerMeasure + (∑ i, (MvPolynomial.degreeOf i P : ℝ)) * Real.log 2 := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_log_norm_coeff_le_logMahlerMeasure_add.solution
