module

public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_zpow_left

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_zpow_left {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ) (hrat : ∀ v ∈ D.support, Place.IsRational v) (hord : ∀ v ∈ D.support, Place.ord v f = 0) : Divisor.evalFun (f ^ n) D = Divisor.evalFun f D ^ n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_zpow_left.solution
