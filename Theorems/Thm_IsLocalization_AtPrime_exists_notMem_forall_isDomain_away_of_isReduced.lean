import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalization_AtPrime_exists_notMem_forall_isDomain_away_of_isReduced

set_option autoImplicit false

universe u v

theorem IsLocalization.AtPrime.exists_notMem_forall_isDomain_away_of_isReduced
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (P : Ideal R) [P.IsPrime]
    (Rp : Type v) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp P] [IsDomain Rp] :
    ∃ f : R, f ∉ P ∧
      ∀ (Rf : Type u) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf], IsDomain Rf := by p2m_exact_reverting @_root_.P2MW.S_IsLocalization_AtPrime_exists_notMem_forall_isDomain_away_of_isReduced.solution
