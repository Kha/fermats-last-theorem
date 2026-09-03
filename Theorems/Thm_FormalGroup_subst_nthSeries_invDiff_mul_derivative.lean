import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_subst_nthSeries_invDiff_mul_derivative

theorem FormalGroup.subst_nthSeries_invDiff_mul_derivative {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm] (n : ℕ) :
    PowerSeries.subst (F.nthSeries n) F.invDiff * PowerSeries.derivative R (F.nthSeries n) = n • F.invDiff := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_subst_nthSeries_invDiff_mul_derivative.solution
