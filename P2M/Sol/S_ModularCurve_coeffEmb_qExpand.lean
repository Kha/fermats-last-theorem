module

public import Definitions.Def_ModularCurve_LaurentCoeff
public import Definitions.Def_ModularCurve_X0
public import Theorems.Thm_ModularCurve_coeffMap_qExpand
public import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_coeffEmb_qExpand

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) :=
  coeffMap_qExpand _ n x
