import Definitions.Def_LanglandsTunnell_LambdaSquared
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_lamSqArch_eq_neg_one_pow_nrComplexPlaces

set_option autoImplicit false

open NumberField

theorem LanglandsTunnell.CubicInduction.lamSqArch_eq_neg_one_pow_nrComplexPlaces
    (K : Type) [Field K] [NumberField K] :
    LanglandsTunnell.CubicInduction.lamSqArch K = (-1 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces K := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_lamSqArch_eq_neg_one_pow_nrComplexPlaces.solution
