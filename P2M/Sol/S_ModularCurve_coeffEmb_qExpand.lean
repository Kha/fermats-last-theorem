module

public import Definitions.Def_ModularCurve_LaurentCoeff
public import Definitions.Def_ModularCurve_X0
import P2M.Sol.S_ModularCurve_coeffMap_qExpand
import P2M.Util

namespace P2MW.S_ModularCurve_coeffEmb_qExpand

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) :=
  coeffMap_qExpand _ n x
end S_ModularCurve_coeffEmb_qExpand
end P2MW

public section
theorem ModularCurve.coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffEmb_qExpand.solution
end
