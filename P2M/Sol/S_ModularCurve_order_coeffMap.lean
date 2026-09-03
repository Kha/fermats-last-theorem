import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
namespace P2MW.S_ModularCurve_order_coeffMap

open ModularCurve
open scoped TensorProduct

theorem solution {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S} (hφ : Function.Injective φ) (x : LaurentSeries R) :
    (coeffMap φ x).order = x.order := by
  by_cases hx : x = 0
  · rw [hx, map_zero, HahnSeries.order_zero, HahnSeries.order_zero]
  have h1 : (coeffMap φ x).coeff x.order ≠ 0 := by
    rw [coeffMap_coeff]
    exact fun h => (HahnSeries.coeff_order_eq_zero.not.mpr hx) ((map_eq_zero_iff φ hφ).mp h)
  have h0 : coeffMap φ x ≠ 0 := fun h => h1 (by rw [h, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  exact HahnSeries.coeff_order_eq_zero.not.mpr h0
    (by rw [coeffMap_coeff, HahnSeries.coeff_eq_zero_of_lt_order h, map_zero])
