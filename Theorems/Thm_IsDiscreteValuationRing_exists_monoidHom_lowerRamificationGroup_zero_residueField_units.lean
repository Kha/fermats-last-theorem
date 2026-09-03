import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_RamificationChain_Wild
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units
attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_monoidHom_lowerRamificationGroup_zero_residueField_units
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)] :
    (∃ θ : ↥(IsLocalRing.lowerRamificationGroup R G 0) →* (IsLocalRing.ResidueField R)ˣ,
        θ.ker = (IsLocalRing.lowerRamificationGroup R G 1).subgroupOf
          (IsLocalRing.lowerRamificationGroup R G 0)) ∧
    IsCyclic (↥(IsLocalRing.lowerRamificationGroup R G 0) ⧸
        (IsLocalRing.lowerRamificationGroup R G 1).subgroupOf
          (IsLocalRing.lowerRamificationGroup R G 0)) ∧
    (∀ p : ℕ, p.Prime → (p : R) ∈ IsLocalRing.maximalIdeal R →
        ¬ p ∣ (IsLocalRing.lowerRamificationGroup R G 1).relIndex
          (IsLocalRing.lowerRamificationGroup R G 0)) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.solution
