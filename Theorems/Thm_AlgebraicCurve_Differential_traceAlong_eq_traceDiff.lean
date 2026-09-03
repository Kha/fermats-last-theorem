import Mathlib
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Differential_traceAlong_eq_traceDiff
open AlgebraicCurve

theorem AlgebraicCurve.Differential.traceAlong_eq_traceDiff
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (h : AlgebraicCurve.SeparableAlong K φ) (η : Ω[F'⁄K]) :
    AlgebraicCurve.Differential.traceAlong φ η =
      (letI := AlgebraicCurve.algebraAlong φ
       haveI := AlgebraicCurve.isScalarTower_along φ
       AlgebraicCurve.traceDiff K F F' η) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Differential_traceAlong_eq_traceDiff.solution
