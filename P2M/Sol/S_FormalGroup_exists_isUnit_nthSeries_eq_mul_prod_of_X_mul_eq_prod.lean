import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
namespace P2MW.S_FormalGroup_exists_isUnit_nthSeries_eq_mul_prod_of_X_mul_eq_prod

set_option autoImplicit false

open IsLocalRing Polynomial

theorem solution
    (T : Type*) [CommRing T] (F : FormalGroup T) (q : ℕ) (g : T[X]) (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)
    (c : ℕ → T) (h : Polynomial.X * g = ∏ a ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a))) :
    ∃ u : PowerSeries T, IsUnit u ∧
      F.nthSeries q = u * ∏ a ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (c a)) := by
  refine ⟨v, hv, ?_⟩
  have hc : ((Polynomial.X * g : T[X]) : PowerSeries T) =
      ∏ a ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (c a)) := by
    rw [h, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C]
  have hc' : (PowerSeries.X : PowerSeries T) * (↑g : PowerSeries T) =
      ∏ a ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (c a)) := by
    simpa [Polynomial.coe_mul, Polynomial.coe_X] using hc
  rw [hF, hc', mul_comm]
