import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_ringEquiv_quotient_map_adicCompletion_quotient

set_option autoImplicit false

open IsLocalRing

theorem AdicCompletion.exists_ringEquiv_quotient_map_adicCompletion_quotient
    (N : Type*) [CommRing N] [IsNoetherianRing N] (I 𝔭 : Ideal N) :
    ∃ e : (AdicCompletion I N ⧸ 𝔭.map (algebraMap N (AdicCompletion I N))) ≃+*
        AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭),
      ∀ x : N, e (Ideal.Quotient.mk _ (algebraMap N (AdicCompletion I N) x)) =
        algebraMap (N ⧸ 𝔭) (AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭)) (Ideal.Quotient.mk 𝔭 x) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringEquiv_quotient_map_adicCompletion_quotient.solution
