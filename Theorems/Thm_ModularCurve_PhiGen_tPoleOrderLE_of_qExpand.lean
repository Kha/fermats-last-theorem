import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_tPoleOrderLE_of_qExpand

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.tPoleOrderLE_of_qExpand {K : Type*} [Field K] {f : LaurentSeries K} {N n : ℕ} [NeZero N] (h : TPoleOrderLE (qExpand K N f) (N * n)) : TPoleOrderLE f n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_of_qExpand.solution
