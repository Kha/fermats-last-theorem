module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ell_le_degree_add_ellZero

@[expose] public section

namespace AlgebraicCurve
theorem ell_le_degree_add_ellZero {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] {D : Divisor K F}
    (hD : 0 ≤ D) [FiniteDimensional K ↥(LSpace (0 : Divisor K F))] :
    (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ell_le_degree_add_ellZero.solution
end AlgebraicCurve
