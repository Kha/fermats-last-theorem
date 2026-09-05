module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_degree_eq_sum_support

@[expose] public section

namespace AlgebraicCurve
theorem Divisor.degree_eq_sum_support {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_degree_eq_sum_support.solution
end AlgebraicCurve
