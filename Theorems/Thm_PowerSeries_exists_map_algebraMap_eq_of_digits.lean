import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_map_algebraMap_eq_of_digits
set_option autoImplicit false
theorem PowerSeries.exists_map_algebraMap_eq_of_digits
    {R R' L : Type*} [CommRing R] [CommRing R'] [CommRing L] [Algebra R L]
    (ι : R →+* R') (I : Ideal R') (t : R') (e : R' →+* PowerSeries L)
    (hι : ∀ r : R, e (ι r) = PowerSeries.C (algebraMap R L r))
    (hI : ∀ i ∈ I, PowerSeries.constantCoeff (e i) = 0)
    (u : PowerSeries R) (ht : e t = u.map (algebraMap R L))
    (hdig : ∀ (z : R') (n : ℕ), ∃ a : ℕ → R, z - ∑ i ∈ Finset.range n, ι (a i) * t ^ i ∈ I ^ n)
    (z : R') : ∃ P : PowerSeries R, e z = P.map (algebraMap R L) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_map_algebraMap_eq_of_digits.solution
