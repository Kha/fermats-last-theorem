import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite

set_option autoImplicit false

universe u v

theorem HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (_ : Fintype (MaximalSpectrum S)) (e : MaximalSpectrum S → S),
      CompleteOrthogonalIdempotents e ∧
      (∀ m : MaximalSpectrum S, e m ∉ m.asIdeal) ∧
      (∀ m m' : MaximalSpectrum S, m ≠ m' → e m ∈ m'.asIdeal) ∧
      (∀ m : MaximalSpectrum S, IsLocalRing (S ⧸ Ideal.span {1 - e m})) := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite.solution
