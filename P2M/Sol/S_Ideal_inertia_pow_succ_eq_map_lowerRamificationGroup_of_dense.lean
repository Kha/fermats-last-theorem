import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import P2M.Util
namespace P2MW.S_Ideal_inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B] (Q : Ideal B)
    {Γ : Type*} [Group Γ] (j : Γ →* G) (hj : ∀ σ : G, (∀ x ∈ Q, σ • x ∈ Q) → σ ∈ j.range)
    {R : Type*} [CommRing R] [IsLocalRing R] [MulSemiringAction Γ R]
    (f : B →+* R) (hf : ∀ (γ : Γ) (x : B), f (j γ • x) = γ • f x)
    (hcomap : ∀ n : ℕ, (IsLocalRing.maximalIdeal R ^ n).comap f = Q ^ n)
    (hdense : ∀ (n : ℕ) (y : R), ∃ x : B, y - f x ∈ IsLocalRing.maximalIdeal R ^ n) (i : ℕ) :
    (Q ^ (i + 1)).inertia G = (IsLocalRing.lowerRamificationGroup R Γ i).map j := by
  ext σ
  constructor
  · intro hσ
    have hσ' : ∀ x : B, σ • x - x ∈ Q ^ (i + 1) := hσ

    obtain ⟨γ, rfl⟩ : σ ∈ j.range := hj σ (fun x hx => by
      have h1 : σ • x - x ∈ Q := Ideal.pow_le_self (Nat.succ_ne_zero i) (hσ' x)
      have h2 : σ • x = (σ • x - x) + x := by abel
      rw [h2]
      exact Q.add_mem h1 hx)
    refine Subgroup.mem_map.mpr ⟨γ, ?_, rfl⟩
    rw [IsLocalRing.mem_lowerRamificationGroup]
    intro y
    obtain ⟨x, hx⟩ := hdense (i + 1) y
    have hy : y = f x + (y - f x) := by abel
    have h1 : γ • f x - f x ∈ IsLocalRing.maximalIdeal R ^ (i + 1) := by
      rw [← hf, ← map_sub, ← Ideal.mem_comap, hcomap]
      exact hσ' x
    have h2 : γ • (y - f x) - (y - f x) ∈ IsLocalRing.maximalIdeal R ^ (i + 1) := by
      refine Ideal.sub_mem _ ?_ hx
      rw [← IsLocalRing.pointwise_smul_maximalIdeal_pow γ (i + 1)]
      exact Ideal.smul_mem_pointwise_smul _ _ _ hx
    have h3 : γ • y - y = (γ • f x - f x) + (γ • (y - f x) - (y - f x)) := by
      conv_lhs => rw [hy]
      rw [smul_add]
      abel
    rw [h3]
    exact Ideal.add_mem _ h1 h2
  · intro hσ
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hσ
    intro x
    change j γ • x - x ∈ Q ^ (i + 1)
    rw [← hcomap, Ideal.mem_comap, map_sub, hf]
    exact (IsLocalRing.mem_lowerRamificationGroup.mp hγ) (f x)
