import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_evalSymm_of_irreducible

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.ModularPolynomialData.evalSymm_of_irreducible {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (hirr : PhiIrreducible data) (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0) (hTmonic : ((swapBivar data.Φ).map evalAtJGen).Monic) (hTdeg : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi N) : EvalSymm data.Φ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_evalSymm_of_irreducible.solution
