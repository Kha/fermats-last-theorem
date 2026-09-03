import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsInvariant_isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal

set_option autoImplicit false

theorem Algebra.IsInvariant.isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal
    {S A : Type*} [CommRing S] [CommRing A] [Algebra S A] [FaithfulSMul S A]
    [IsNoetherianRing S] [IsNoetherianRing A]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G S A] [Algebra.IsInvariant S A G]
    (hA : ∀ (P : Ideal A) (_ : P.IsMaximal),
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P))
    (q : Ideal S) [q.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime q), IsDiscreteValuationRing (Localization.AtPrime q) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsInvariant_isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal.solution
