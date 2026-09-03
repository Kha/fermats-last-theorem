import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem

theorem ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (V : ValuationSubring K) (hRV : ∀ r : R, algebraMap R K r ∈ V) (hV : V ≠ ⊤) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum R, V = v.valuationSubringAtPrime K ∧
      ∀ r : R, r ∈ v.asIdeal ↔ algebraMap R K r ∈ V.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem.solution
