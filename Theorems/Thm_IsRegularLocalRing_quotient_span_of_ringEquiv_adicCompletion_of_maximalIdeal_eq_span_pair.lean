import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_quotient_span_of_ringEquiv_adicCompletion_of_maximalIdeal_eq_span_pair

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsRegularLocalRing.quotient_span_of_ringEquiv_adicCompletion_of_maximalIdeal_eq_span_pair
    {R' : Type*} [CommRing R'] [IsRegularLocalRing R']
    (ϖ' τ : R') (hmax : maximalIdeal R' = Ideal.span {ϖ', τ}) (hdim : ringKrullDim R' = 2)
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (ϖS : S)
    (ι : AdicCompletion (maximalIdeal S) S ≃+* AdicCompletion (maximalIdeal R') R')
    (hι : ι (algebraMap S _ ϖS) = algebraMap R' _ ϖ') :
    IsRegularLocalRing (S ⧸ Ideal.span {ϖS}) ∧ ringKrullDim (S ⧸ Ideal.span {ϖS}) = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_quotient_span_of_ringEquiv_adicCompletion_of_maximalIdeal_eq_span_pair.solution
