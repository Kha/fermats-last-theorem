import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isRegularLocalRing_and_ringKrullDim_eq_two_of_finite_of_maximalIdeal_le_span_pair_sup_sq

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.isRegularLocalRing_and_ringKrullDim_eq_two_of_finite_of_maximalIdeal_le_span_pair_sup_sq
    (S₀ : Type) [CommRing S₀] [IsDomain S₀] [IsNoetherianRing S₀] [IsLocalRing S₀] (hdim₀ : ringKrullDim S₀ = 2)
    (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra S₀ S] [Module.Finite S₀ S]
    (hinj : Function.Injective (algebraMap S₀ S))
    (ϖ y : S) (hgen : maximalIdeal S ≤ Ideal.span {ϖ, y} ⊔ maximalIdeal S ^ 2)
    (hϖ : ϖ ∈ maximalIdeal S) (hy : y ∈ maximalIdeal S) :
    IsRegularLocalRing S ∧ ringKrullDim S = 2 ∧ maximalIdeal S = Ideal.span {ϖ, y} := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isRegularLocalRing_and_ringKrullDim_eq_two_of_finite_of_maximalIdeal_le_span_pair_sup_sq.solution
