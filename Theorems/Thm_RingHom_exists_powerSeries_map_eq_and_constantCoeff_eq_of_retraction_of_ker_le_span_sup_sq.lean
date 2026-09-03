import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq

set_option autoImplicit false

theorem RingHom.exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq
    {R R' L : Type*} [CommRing R] [CommRing R'] [CommRing L] [Algebra R L]
    (ι : R →+* R') (π : R' →+* R) (hπ : π.comp ι = RingHom.id R)
    (t : R') (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (e : R' →+* PowerSeries L)
    (hι : ∀ r : R, e (ι r) = PowerSeries.C (algebraMap R L r))
    (hI : ∀ i ∈ RingHom.ker π, PowerSeries.constantCoeff (e i) = 0)
    (u : PowerSeries R) (hu : e t = u.map (algebraMap R L))
    (z : R') :
    ∃ P : PowerSeries R, e z = P.map (algebraMap R L) ∧ PowerSeries.constantCoeff P = π z := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq.solution
