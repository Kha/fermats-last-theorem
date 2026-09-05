module

public import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Sol.S_ModularCurve_coeffMap_injective
import P2M.Util

namespace P2MW.S_ModularCurve_coeffEmb_injective

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (ModularCurve.coeffEmb L) :=
  coeffMap_injective (FaithfulSMul.algebraMap_injective ℚ L)
end S_ModularCurve_coeffEmb_injective
end P2MW

public section
theorem ModularCurve.coeffEmb_injective (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (ModularCurve.coeffEmb L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffEmb_injective.solution
end
