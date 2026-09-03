import Definitions.Def_MvPolynomial_LogMahlerMeasure
import P2M.Util
import P2M.Sol.S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero

theorem MvPolynomial.ae_restrict_torusBox_eval_circleMap_ne_zero {n : ℕ} {P : MvPolynomial (Fin n) ℂ} (hP : P ≠ 0) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (MvPolynomial.torusBox n)),
      MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero.solution
