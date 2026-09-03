import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_nonempty_quotient_pow_algEquiv_localization_atPrime

set_option autoImplicit false

open scoped TensorProduct

theorem IsArtinianRing.nonempty_quotient_pow_algEquiv_localization_atPrime
    (A : Type*) [CommRing A] [IsArtinianRing A] (𝔫 : Ideal A) [𝔫.IsMaximal]
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) :
    Nonempty ((A ⧸ 𝔫 ^ N) ≃ₐ[A] Localization.AtPrime 𝔫) := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_nonempty_quotient_pow_algEquiv_localization_atPrime.solution
