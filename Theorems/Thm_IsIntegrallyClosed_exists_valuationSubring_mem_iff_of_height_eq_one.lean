import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one

theorem IsIntegrallyClosed.exists_valuationSubring_mem_iff_of_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ∃ V : ValuationSubring K, IsPrincipalIdealRing V ∧ V ≠ ⊤ ∧
      ∀ x : K, x ∈ V ↔ ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one.solution
