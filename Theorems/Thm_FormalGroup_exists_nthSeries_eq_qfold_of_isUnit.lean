import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_nthSeries_eq_qfold_of_isUnit

theorem FormalGroup.exists_nthSeries_eq_qfold_of_isUnit {R : Type*} [CommRing R] (F : FormalGroup R) [F.IsComm] {q : ℕ}
    (hq : 2 ≤ q) (hunit : ∀ k : ℕ, 1 ≤ k → ¬ q ∣ k → IsUnit (k : R)) :
    ∃ h g : PowerSeries R,
      F.nthSeries q = q • PowerSeries.X + (q : R) • (PowerSeries.X ^ 2 * h) + PowerSeries.X ^ q * g := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_nthSeries_eq_qfold_of_isUnit.solution
