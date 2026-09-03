import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_swapBivar_monic_of_coeff_bounds

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.swapBivar_monic_of_coeff_bounds {Φ : Polynomial (Polynomial ℤ)} {d : ℕ} (h0 : (Φ.coeff 0).Monic) (h0deg : (Φ.coeff 0).natDegree = d) (hk : ∀ k, k ≠ 0 → (Φ.coeff k).degree < (d : WithBot ℕ)) : (swapBivar Φ).Monic ∧ (swapBivar Φ).natDegree = d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_swapBivar_monic_of_coeff_bounds.solution
