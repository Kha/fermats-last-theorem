import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_RamificationChain_Wild
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one

set_option autoImplicit false

theorem IsDiscreteValuationRing.ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    [PerfectField (IsLocalRing.ResidueField R)]
    {σ : G} (hσ : σ ∈ IsLocalRing.lowerRamificationGroup R G 1)
    {n : ℕ} (hn : 1 ≤ n) (hσn : σ ^ p ^ n ≠ 1) :
    (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ (n - 1))).toNat ≡
      (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ n)).toNat [MOD p ^ n] := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.solution
