module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finiteDimensional_lSpace

@[expose] public section

namespace AlgebraicCurve
theorem finiteDimensional_lSpace {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [hL0 : FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    (D : Divisor K F) : FiniteDimensional K ↥(LSpace D) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finiteDimensional_lSpace.solution
end AlgebraicCurve
