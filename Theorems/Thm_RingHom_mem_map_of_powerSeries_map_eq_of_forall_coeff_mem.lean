import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_mem_map_of_powerSeries_map_eq_of_forall_coeff_mem

set_option autoImplicit false

theorem RingHom.mem_map_of_powerSeries_map_eq_of_forall_coeff_mem
    {R R' L : Type*} [CommRing R] [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    [CommRing L] [Algebra R L] (hinj : Function.Injective (algebraMap R L))
    (ι : R →+* R') (π : R' →+* R) (hπ : π.comp ι = RingHom.id R)
    (t : R') (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (htm : t ∈ IsLocalRing.maximalIdeal R')
    (e : R' →+* PowerSeries L) (hι : ∀ r : R, e (ι r) = PowerSeries.C (algebraMap R L r))
    (hI : ∀ i ∈ RingHom.ker π, PowerSeries.constantCoeff (e i) = 0)
    (u : PowerSeries R) (hu : e t = u.map (algebraMap R L)) (hu1 : IsUnit (PowerSeries.coeff 1 u))
    (𝔞 : Ideal R) (z : R') (P : PowerSeries R) (hP : e z = P.map (algebraMap R L))
    (hPa : ∀ n : ℕ, PowerSeries.coeff n P ∈ 𝔞) :
    z ∈ 𝔞.map ι := by p2m_exact_reverting @_root_.P2MW.S_RingHom_mem_map_of_powerSeries_map_eq_of_forall_coeff_mem.solution
