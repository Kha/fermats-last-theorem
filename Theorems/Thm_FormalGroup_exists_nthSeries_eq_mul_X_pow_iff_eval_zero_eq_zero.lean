import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero

set_option autoImplicit false

open IsLocalRing Polynomial

theorem FormalGroup.exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero
    (T : Type*) [CommRing T] [IsLocalRing T]
    (F : FormalGroup T) [F.IsComm] (q : ℕ) [Fact q.Prime]
    (g : T[X]) (hmonic : g.Monic) (hdeg : g.natDegree = q - 1)
    (hdist : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v) :
    ((∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ q) ↔ g.eval 0 = 0) ∧
      (g.eval 0 = 0 ↔ (q : T) = 0) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero.solution
