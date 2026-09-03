import Mathlib.Analysis.Polynomial.MahlerMeasure
import P2M.Util
import P2M.Sol.S_Polynomial_log_norm_coeff_le_logMahlerMeasure_add

theorem Polynomial.log_norm_coeff_le_logMahlerMeasure_add {p : Polynomial ℂ} {k : ℕ} (hk : p.coeff k ≠ 0) :
    Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure + p.natDegree * Real.log 2 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_log_norm_coeff_le_logMahlerMeasure_add.solution
