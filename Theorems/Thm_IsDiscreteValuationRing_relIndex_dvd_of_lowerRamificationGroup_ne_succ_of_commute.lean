import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_RamificationChain_Wild
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute
attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype

set_option autoImplicit false

theorem IsDiscreteValuationRing.relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    (hcomm : ∀ s ∈ IsLocalRing.lowerRamificationGroup R G 0,
      ∀ t ∈ IsLocalRing.lowerRamificationGroup R G 0, Commute s t)
    {i : ℕ} (hi : 1 ≤ i)
    (hjump : IsLocalRing.lowerRamificationGroup R G i ≠ IsLocalRing.lowerRamificationGroup R G (i + 1)) :
    (IsLocalRing.lowerRamificationGroup R G 1).relIndex (IsLocalRing.lowerRamificationGroup R G 0) ∣ i := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.solution
