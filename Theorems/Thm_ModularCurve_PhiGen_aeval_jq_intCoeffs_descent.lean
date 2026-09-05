module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.aeval_jq_intCoeffs_descent (P : Polynomial ℚ) (hP : IntCoeffs (Polynomial.aeval jq P)) (k : ℕ) : ∃ z : ℤ, P.coeff k = (z : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.solution
