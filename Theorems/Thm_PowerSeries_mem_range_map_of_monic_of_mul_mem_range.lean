import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_mem_range_map_of_monic_of_mul_mem_range

theorem PowerSeries.mem_range_map_of_monic_of_mul_mem_range
    {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (g : PowerSeries K) (Φ : Polynomial (PowerSeries R)) (hΦ : Φ.Monic)
    (hroot : Polynomial.eval₂ (PowerSeries.map (algebraMap R K)) g Φ = 0)
    (h : PowerSeries R) (h0 : h ≠ 0)
    (hmul : PowerSeries.map (algebraMap R K) h * g ∈ (PowerSeries.map (algebraMap R K)).range) :
    g ∈ (PowerSeries.map (algebraMap R K)).range := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_mem_range_map_of_monic_of_mul_mem_range.solution
