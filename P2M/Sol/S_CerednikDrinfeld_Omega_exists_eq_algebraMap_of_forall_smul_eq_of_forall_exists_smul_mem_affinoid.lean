import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_v_apply_le
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) (Λ : Subgroup G)
    (N : ℕ) (hcpt : ∀ z : ↥(upperHalfPlane K₀ K), ∃ γ ∈ Λ, ((ρ γ • z : ↥(upperHalfPlane K₀ K)) : K) ∈ affinoid ϖ N)
    (f : ↥(holRing ϖ)) (hinv : ∀ γ ∈ Λ, ρ γ • f = f) :
    ∃ c : K, f = algebraMap K ↥(holRing ϖ) c := by

  obtain ⟨B, hB⟩ := ((mem_holRing_iff ϖ _).mp f.2 N).bounded

  have hb : ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≤ Valued.v B := by
    intro z
    obtain ⟨γ, hγ, hz⟩ := hcpt z
    have h1 : (f : ↥(upperHalfPlane K₀ K) → K) z =
        (f : ↥(upperHalfPlane K₀ K) → K) (ρ γ • z) := by
      conv_lhs => rw [← hinv γ⁻¹ (Λ.inv_mem hγ)]
      rw [coe_smul_holRing_apply, map_inv, inv_inv]
    rw [h1]
    have h2 := hB ⟨((ρ γ • z : ↥(upperHalfPlane K₀ K)) : K), hz⟩
    have h3 : restrictAffinoid ϖ N (f : ↥(upperHalfPlane K₀ K) → K) ⟨((ρ γ • z : ↥(upperHalfPlane K₀ K)) : K), hz⟩ =
        (f : ↥(upperHalfPlane K₀ K) → K) (ρ γ • z) := by
      rfl
    rwa [h3] at h2
  exact CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_v_apply_le K₀ K ϖ hrk hex hfin f B hb
