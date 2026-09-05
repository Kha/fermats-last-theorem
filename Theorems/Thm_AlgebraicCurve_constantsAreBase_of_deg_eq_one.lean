module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_constantsAreBase_of_deg_eq_one

@[expose] public section
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue

theorem AlgebraicCurve.constantsAreBase_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (v₀ : AlgebraicCurve.Place K F) (hdeg : v₀.deg = 1) :
    AlgebraicCurve.ConstantsAreBase K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_constantsAreBase_of_deg_eq_one.solution
