import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_derivative_eval_ne_zero_of_nthSeries_eq_mul

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.derivative_eval_ne_zero_of_nthSeries_eq_mul
    (q : ℕ) {V : Type*} [CommRing V] [IsDomain V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (hqV : (q : V) ≠ 0) (G : FormalGroup V) [G.IsComm]
    (P : Polynomial V) (U : PowerSeries V) (hU : IsUnit U)
    (hq : G.nthSeries q = (P : PowerSeries V) * U)
    (r : V) (hr : r ∈ maximalIdeal V) (hPr : P.eval r = 0) :
    (Polynomial.derivative P).eval r ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_derivative_eval_ne_zero_of_nthSeries_eq_mul.solution
