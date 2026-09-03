import Definitions.Def_MvPolynomial_LogMahlerMeasure
import P2M.Util
import P2M.Sol.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv

theorem MvPolynomial.logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    P.logMahlerMeasure = ((2 * Real.pi)⁻¹) ^ n *
      ∫ θ' in MvPolynomial.torusBox n,
        (Polynomial.map (MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ' i)))
          (MvPolynomial.finSuccEquiv ℂ n P)).logMahlerMeasure := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_logMahlerMeasure_eq_mul_integral_logMahlerMeasure_map_finSuccEquiv.solution
