import Definitions.Def_ModularCurve_CycSubRootBridgeN
import P2M.Util
import P2M.Sol.S_ModularCurve_TatePoint_fullKernelDiscAt_univ
attribute [-simp] WeierstrassCurve.veluPointMap2_zero

open scoped Classical

theorem ModularCurve.TatePoint.fullKernelDiscAt_univ (N : ℕ) [NeZero N] {L : Type*} [Field L] [DecidableEq L]
    [IsAlgClosed L] (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L) [W.IsElliptic] (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = N) : (W.fullKernelQuotient Q N).Δ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TatePoint_fullKernelDiscAt_univ.solution
