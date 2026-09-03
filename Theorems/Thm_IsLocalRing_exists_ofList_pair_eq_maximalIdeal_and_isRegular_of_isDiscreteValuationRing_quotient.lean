import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient

set_option autoImplicit false

theorem IsLocalRing.exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] (ϖ : A) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖ0 : ϖ ≠ 0)
    [IsDomain (A ⧸ Ideal.span {ϖ})] [IsDiscreteValuationRing (A ⧸ Ideal.span {ϖ})] :
    ∃ t : A, Ideal.ofList [ϖ, t] = IsLocalRing.maximalIdeal A ∧ RingTheory.Sequence.IsRegular A [ϖ, t] := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient.solution
