import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete

universe u

theorem IsLocalRing.exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (I : ℕ → Ideal A) (hI : Antitone I) (hinf : ⨅ n, I n = ⊥) (N : ℕ) :
    ∃ n, I n ≤ IsLocalRing.maximalIdeal A ^ N := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete.solution
