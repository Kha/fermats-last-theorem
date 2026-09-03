import Definitions.Def_ModularCurve_TateSlots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_toricPoint_level_mul

open HahnSeries
theorem ModularCurve.toricPoint_level_mul (K : Type*) [Field K] (p a : ℕ) [NeZero a] (c : K) :
    toricPoint K (a * p) c =
      (qExpand K a (toricPoint K p c).1, qExpand K a (toricPoint K p c).2) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_toricPoint_level_mul.solution
