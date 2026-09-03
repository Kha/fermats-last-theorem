import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

theorem IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r) :
    ∃ r : R, algebraMap R K r = x := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one.solution
