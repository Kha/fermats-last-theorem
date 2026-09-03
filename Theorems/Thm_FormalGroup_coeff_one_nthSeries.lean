import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_coeff_one_nthSeries

theorem FormalGroup.coeff_one_nthSeries {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (F.nthSeries n) = (n : R) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_coeff_one_nthSeries.solution
