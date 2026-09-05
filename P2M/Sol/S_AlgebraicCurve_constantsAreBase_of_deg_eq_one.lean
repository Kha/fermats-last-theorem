module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
public import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_exists_isRational
public import P2M.Sol.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicCurve_constantsAreBase_of_deg_eq_one
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (v₀ : AlgebraicCurve.Place K F) (hdeg : v₀.deg = 1) :
    AlgebraicCurve.ConstantsAreBase K F :=
  AlgebraicCurve.constantsAreBase_of_exists_isRational v₀ ((v₀.isRational_iff_deg_eq_one).mpr hdeg)
    (hdeg ▸ one_ne_zero)
