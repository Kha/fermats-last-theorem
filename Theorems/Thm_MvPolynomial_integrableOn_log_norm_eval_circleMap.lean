import Definitions.Def_MvPolynomial_LogMahlerMeasure
import P2M.Util
import P2M.Sol.S_MvPolynomial_integrableOn_log_norm_eval_circleMap

theorem MvPolynomial.integrableOn_log_norm_eval_circleMap {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    MeasureTheory.IntegrableOn
      (fun θ : Fin n → ℝ ↦ Real.log ‖MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P‖)
      (MvPolynomial.torusBox n) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_integrableOn_log_norm_eval_circleMap.solution
