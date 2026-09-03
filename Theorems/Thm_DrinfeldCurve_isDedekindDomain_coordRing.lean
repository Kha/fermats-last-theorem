import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_DrinfeldCurve_CoordRing
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_isDedekindDomain_coordRing

set_option autoImplicit false

open DrinfeldCurve

theorem DrinfeldCurve.isDedekindDomain_coordRing (q : ℕ) [Fact q.Prime] (k : Type) [Field k]
    [Algebra (GaloisField q 2) k] [IsAlgClosed k] [IsDomain (CoordRing q k)] :
    IsDedekindDomain (CoordRing q k) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_isDedekindDomain_coordRing.solution
