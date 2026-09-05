module

public import Definitions.Def_ModularCurve_AtkinLehner
public import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
public import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_deg_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] :
    (cuspInftyBar N).deg = 1 :=
  ModularCurve.deg_qInftyPlaceBar (AlgebraicClosure ℚ) _
