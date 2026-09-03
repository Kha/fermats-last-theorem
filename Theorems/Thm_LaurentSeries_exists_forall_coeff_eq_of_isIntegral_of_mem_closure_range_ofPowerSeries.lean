import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_exists_forall_coeff_eq_of_isIntegral_of_mem_closure_range_ofPowerSeries

set_option autoImplicit false

theorem LaurentSeries.exists_forall_coeff_eq_of_isIntegral_of_mem_closure_range_ofPowerSeries
    {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K]
    (i : R →+* K) (hi : Function.Injective i)
    (x : LaurentSeries K)
    (hx : x ∈ Subfield.closure (Set.range ((HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map i))))
    (S : Subring (LaurentSeries K)) (hS : ∀ z ∈ S, ∀ n : ℤ, z.coeff n ∈ Set.range i)
    (hint : IsIntegral ↥S x) :
    ∃ y : LaurentSeries R, ∀ n : ℤ, i (y.coeff n) = x.coeff n := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_exists_forall_coeff_eq_of_isIntegral_of_mem_closure_range_ofPowerSeries.solution
