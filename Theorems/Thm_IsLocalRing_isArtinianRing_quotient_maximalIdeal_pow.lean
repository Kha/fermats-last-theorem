import Mathlib.RingTheory.Artinian.Ring
import P2M.Util
import P2M.Sol.S_IsLocalRing_isArtinianRing_quotient_maximalIdeal_pow

theorem IsLocalRing.isArtinianRing_quotient_maximalIdeal_pow
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (m : ℕ) :
    IsArtinianRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isArtinianRing_quotient_maximalIdeal_pow.solution
