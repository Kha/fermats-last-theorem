module

public import Mathlib
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
public import Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification

@[expose] public section

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum (K : Type*) [Field K] [DecidableEq (RatFunc K)] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) : placeInfty K ≠ Place.ofHeightOneSpectrum w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum
