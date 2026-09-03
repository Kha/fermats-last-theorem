import Definitions.Def_DrinfeldCurve_CoordRing
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_isDomain_coordRing_of_ne_one

set_option autoImplicit false

universe u

theorem DrinfeldCurve.isDomain_coordRing_of_ne_one (q : ℕ) (hq : q ≠ 1) (k : Type u) [Field k] :
    IsDomain (DrinfeldCurve.CoordRing q k) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_isDomain_coordRing_of_ne_one.solution
