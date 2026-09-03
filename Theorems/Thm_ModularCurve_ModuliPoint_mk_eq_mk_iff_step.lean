import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import P2M.Util
import P2M.Sol.S_ModularCurve_ModuliPoint_mk_eq_mk_iff_step

theorem ModularCurve.ModuliPoint.mk_eq_mk_iff_step
    {N : ℕ} {L : Type*} [Field L] [DecidableEq L] (P Q : ModularCurve.Gamma0Pair N L) :
    (Quot.mk _ P : ModularCurve.ModuliPoint N L) = Quot.mk _ Q ↔ ModularCurve.Gamma0Pair.Step P Q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModuliPoint_mk_eq_mk_iff_step.solution
