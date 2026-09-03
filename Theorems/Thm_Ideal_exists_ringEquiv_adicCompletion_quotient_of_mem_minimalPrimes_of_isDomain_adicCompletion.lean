import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion

set_option autoImplicit false

theorem Ideal.exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion
    (S : Type) [CommRing S] [IsNoetherianRing S]
    (𝔮 : Ideal S) (h𝔮 : 𝔮 ∈ minimalPrimes S)
    (x : Ideal S) [x.IsMaximal] (hle : 𝔮 ≤ x)
    (hdom : IsDomain (AdicCompletion x S)) :
    ∃ e : AdicCompletion (x.map (Ideal.Quotient.mk 𝔮)) (S ⧸ 𝔮) ≃+* AdicCompletion x S,
      ∀ s : S, e (algebraMap (S ⧸ 𝔮) (AdicCompletion (x.map (Ideal.Quotient.mk 𝔮)) (S ⧸ 𝔮)) (Ideal.Quotient.mk 𝔮 s)) =
        algebraMap S (AdicCompletion x S) s := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion.solution
