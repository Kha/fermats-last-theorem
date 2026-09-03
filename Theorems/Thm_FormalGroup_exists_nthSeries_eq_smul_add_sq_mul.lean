import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_nthSeries_eq_smul_add_sq_mul

theorem FormalGroup.exists_nthSeries_eq_smul_add_sq_mul {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    ∃ G : PowerSeries R, F.nthSeries n = (n : R) • PowerSeries.X + PowerSeries.X ^ 2 * G := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_nthSeries_eq_smul_add_sq_mul.solution
