import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot

set_option autoImplicit false

universe u

theorem IsLocalRing.exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : ℕ → Ideal A) (hK : Antitone K) (hinf : ⨅ w, K w = ⊥) (N : ℕ) :
    ∃ w : ℕ, K w ≤ IsLocalRing.maximalIdeal A ^ N := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot.solution
