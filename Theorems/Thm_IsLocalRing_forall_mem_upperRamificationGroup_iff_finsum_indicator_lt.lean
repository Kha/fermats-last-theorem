import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import P2M.Util
import P2M.Sol.S_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt

set_option autoImplicit false
open scoped Classical in

theorem IsLocalRing.forall_mem_upperRamificationGroup_iff_finsum_indicator_lt
    {R : Type*} [CommRing R] [IsLocalRing R] {Γ : Type*} [Group Γ] [Finite Γ] [MulSemiringAction Γ R]
    {A : Type*} [CommGroup A] (χ : Γ →* A)
    (hfin : ∃ N : ℕ, ∀ σ ∈ IsLocalRing.lowerRamificationGroup R Γ N, χ σ = 1)
    (hram : ¬ ∀ σ ∈ IsLocalRing.lowerRamificationGroup R Γ 0, χ σ = 1)
    (u : ℚ) (hu : 0 ≤ u) :
    (∀ σ ∈ IsLocalRing.upperRamificationGroup R Γ u, χ σ = 1) ↔
      ∑ᶠ i : ℕ,
          (Nat.card (IsLocalRing.lowerRamificationGroup R Γ (i + 1)) : ℚ) /
              (Nat.card (IsLocalRing.lowerRamificationGroup R Γ 0) : ℚ) *
            (if ∀ σ ∈ IsLocalRing.lowerRamificationGroup R Γ (i + 1), χ σ = 1 then 0 else 1) < u := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt.solution
