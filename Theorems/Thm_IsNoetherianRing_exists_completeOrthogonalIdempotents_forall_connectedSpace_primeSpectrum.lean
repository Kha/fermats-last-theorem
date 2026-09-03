import Mathlib
import P2M.Util
import P2M.Sol.S_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_connectedSpace_primeSpectrum

universe u

theorem IsNoetherianRing.exists_completeOrthogonalIdempotents_forall_connectedSpace_primeSpectrum
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    ∃ (m : ℕ) (e : Fin m → R), CompleteOrthogonalIdempotents e ∧
      ∀ i, ConnectedSpace (PrimeSpectrum (Localization.Away (e i))) := by p2m_exact_reverting @_root_.P2MW.S_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_connectedSpace_primeSpectrum.solution
