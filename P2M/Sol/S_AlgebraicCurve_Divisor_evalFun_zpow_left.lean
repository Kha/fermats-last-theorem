module

public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
public import Theorems.Thm_AlgebraicCurve_Place_evalAt_zpow
import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_zpow_left

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ) (hrat : ∀ v ∈ D.support, Place.IsRational v) (hord : ∀ v ∈ D.support, Place.ord v f = 0) : Divisor.evalFun (f ^ n) D = Divisor.evalFun f D ^ n := by
  rw [evalFun_def, evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [AlgebraicCurve.Place.evalAt_zpow v (hrat v hv) hf (hord v hv) n, ← zpow_mul, ← zpow_mul, mul_comm]
