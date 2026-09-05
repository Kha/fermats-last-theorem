module

public import Definitions.Def_ModularCurve_LaurentCoeff
public import P2M.Util
public import P2M.Sol.S_ModularCurve_order_coeffEmb

@[expose] public section

open ModularCurve

theorem ModularCurve.order_coeffEmb (L : Type*) [Field L] [Algebra ℚ L] (x : LaurentSeries ℚ) : (coeffEmb L x).order = x.order := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_order_coeffEmb.solution
