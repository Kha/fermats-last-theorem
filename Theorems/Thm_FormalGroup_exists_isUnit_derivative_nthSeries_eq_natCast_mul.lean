import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_isUnit_derivative_nthSeries_eq_natCast_mul

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.exists_isUnit_derivative_nthSeries_eq_natCast_mul
    {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm] (n : ℕ) :
    ∃ u : PowerSeries R, IsUnit u ∧ PowerSeries.derivative R (F.nthSeries n) = (n : PowerSeries R) * u := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_isUnit_derivative_nthSeries_eq_natCast_mul.solution
