import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_tPoleOrderLE_coeffEmb_iff

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.tPoleOrderLE_coeffEmb_iff {K : Type*} [Field K] [Algebra ℚ K] (f : LaurentSeries ℚ) (n : ℕ) : TPoleOrderLE (coeffEmb K f) n ↔ TPoleOrderLE f n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_coeffEmb_iff.solution
