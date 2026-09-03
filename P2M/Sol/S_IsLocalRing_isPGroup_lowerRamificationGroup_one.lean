import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Theorems.Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ
import P2M.Util
namespace P2MW.S_IsLocalRing_isPGroup_lowerRamificationGroup_one

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hsep : ⨅ n, IsLocalRing.maximalIdeal R ^ n = ⊥) :
    IsPGroup p (IsLocalRing.lowerRamificationGroup R G 1) := by
  obtain ⟨N, hN⟩ := IsLocalRing.exists_lowerRamificationGroup_eq_bot (R := R) (G := G) hsep
  intro σ
  refine ⟨N, ?_⟩
  have key : ∀ k : ℕ, (σ : G) ^ p ^ k ∈ IsLocalRing.lowerRamificationGroup R G (k + 1) := by
    intro k
    induction k with
    | zero => simpa using σ.2
    | succ k ih =>
      rw [pow_succ, pow_mul]
      exact IsLocalRing.pow_mem_lowerRamificationGroup_succ hp (Nat.succ_le_succ (Nat.zero_le k)) ih
  have h := key N
  rw [hN (N + 1) (Nat.le_succ N), Subgroup.mem_bot] at h
  exact Subtype.ext (by simpa using h)
