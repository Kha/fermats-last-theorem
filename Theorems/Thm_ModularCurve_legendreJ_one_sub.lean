module

public import Mathlib
public import Definitions.Def_ModularCurve_LegendreJ
import P2M.Util
import P2M.Sol.S_ModularCurve_legendreJ_one_sub

@[expose] public section

open ModularCurve
theorem ModularCurve.legendreJ_one_sub {K : Type*} [Field K] (t : K) : legendreJ (1 - t) = legendreJ t := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_legendreJ_one_sub.solution
