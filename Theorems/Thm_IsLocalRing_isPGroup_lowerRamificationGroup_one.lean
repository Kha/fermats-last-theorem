import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import P2M.Util
import P2M.Sol.S_IsLocalRing_isPGroup_lowerRamificationGroup_one

theorem IsLocalRing.isPGroup_lowerRamificationGroup_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hsep : ⨅ n, IsLocalRing.maximalIdeal R ^ n = ⊥) :
    IsPGroup p (IsLocalRing.lowerRamificationGroup R G 1) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isPGroup_lowerRamificationGroup_one.solution
