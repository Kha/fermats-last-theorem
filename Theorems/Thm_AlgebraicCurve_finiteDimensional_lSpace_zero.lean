import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finiteDimensional_lSpace_zero

set_option autoImplicit false

noncomputable section

universe u v

theorem AlgebraicCurve.finiteDimensional_lSpace_zero
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] [Nonempty (Place K F)] :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finiteDimensional_lSpace_zero.solution
