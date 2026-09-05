module

public import Definitions.Def_ModularCurve_JqCoeff
public import Definitions.Def_ModularCurve_PhiGen
public import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily
public import Theorems.Thm_ModularCurve_modularPolynomialFamily
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_isIntegral_jqNModC_all

open ModularCurve

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) :=
  isIntegral_jqNModC_all_of_modularPolynomialFamily K modularPolynomialFamily N

