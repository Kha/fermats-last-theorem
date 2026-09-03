import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_intCoeffs_jq_pow

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.intCoeffs_jq_pow (n : ℕ) : IntCoeffs (jq ^ n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_intCoeffs_jq_pow.solution
