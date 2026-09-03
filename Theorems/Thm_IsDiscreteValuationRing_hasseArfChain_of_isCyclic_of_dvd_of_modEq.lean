import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_RamificationChain_Wild
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq

set_option autoImplicit false

theorem IsDiscreteValuationRing.hasseArfChain_of_isCyclic_of_dvd_of_modEq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    [IsCyclic ↥(IsLocalRing.lowerRamificationGroup R G 0)]
    {p : ℕ} (hp : p.Prime)
    (hG1 : IsPGroup p ↥(IsLocalRing.lowerRamificationGroup R G 1))
    (hcop : ¬ p ∣ (IsLocalRing.lowerRamificationGroup R G 1).relIndex (IsLocalRing.lowerRamificationGroup R G 0))
    (htame : ∀ j : ℕ, 1 ≤ j →
      IsLocalRing.lowerRamificationGroup R G j ≠ IsLocalRing.lowerRamificationGroup R G (j + 1) →
        (IsLocalRing.lowerRamificationGroup R G 1).relIndex (IsLocalRing.lowerRamificationGroup R G 0) ∣ j)
    (hwild : ∀ σ ∈ IsLocalRing.lowerRamificationGroup R G 1, ∀ n : ℕ, 1 ≤ n → σ ^ p ^ n ≠ 1 →
      (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ (n - 1))).toNat ≡
        (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ n)).toNat [MOD p ^ n]) :
    RamificationChain.HasseArfChain (IsLocalRing.lowerRamificationGroup R G) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq.solution
