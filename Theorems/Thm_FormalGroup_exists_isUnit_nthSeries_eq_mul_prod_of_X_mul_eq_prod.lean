import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_isUnit_nthSeries_eq_mul_prod_of_X_mul_eq_prod

set_option autoImplicit false

open IsLocalRing Polynomial

theorem FormalGroup.exists_isUnit_nthSeries_eq_mul_prod_of_X_mul_eq_prod
    (T : Type*) [CommRing T] (F : FormalGroup T) (q : ℕ) (g : T[X]) (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)
    (c : ℕ → T) (h : Polynomial.X * g = ∏ a ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a))) :
    ∃ u : PowerSeries T, IsUnit u ∧
      F.nthSeries q = u * ∏ a ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (c a)) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_isUnit_nthSeries_eq_mul_prod_of_X_mul_eq_prod.solution
