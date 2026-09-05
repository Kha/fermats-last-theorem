module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_constantsAreBase_of_exists_isRational

@[expose] public section
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue

theorem AlgebraicCurve.constantsAreBase_of_exists_isRational {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (v₀ : AlgebraicCurve.Place K F) (hrat : v₀.IsRational) (hdeg : v₀.deg ≠ 0) :
    AlgebraicCurve.ConstantsAreBase K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_constantsAreBase_of_exists_isRational.solution
