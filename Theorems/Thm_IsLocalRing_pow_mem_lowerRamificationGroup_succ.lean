import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import P2M.Util
import P2M.Sol.S_IsLocalRing_pow_mem_lowerRamificationGroup_succ

open scoped Pointwise commutatorElement
open IsLocalRing
theorem IsLocalRing.pow_mem_lowerRamificationGroup_succ {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    {p : ℕ} (hp : (p : R) ∈ maximalIdeal R) {i : ℕ} (hi : 1 ≤ i) {σ : G}
    (hσ : σ ∈ lowerRamificationGroup R G i) :
    σ ^ p ∈ lowerRamificationGroup R G (i + 1) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_pow_mem_lowerRamificationGroup_succ.solution
