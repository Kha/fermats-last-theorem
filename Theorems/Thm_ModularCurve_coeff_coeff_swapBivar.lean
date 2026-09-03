import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_coeff_swapBivar

open ModularCurve Polynomial
theorem ModularCurve.coeff_coeff_swapBivar (Φ : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    ((swapBivar Φ).coeff j).coeff i = (Φ.coeff i).coeff j := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_coeff_swapBivar.solution
