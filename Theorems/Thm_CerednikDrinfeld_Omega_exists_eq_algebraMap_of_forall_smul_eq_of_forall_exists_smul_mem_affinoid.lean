import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega hiding exists_eq_algebraMap_of_forall_v_apply_le

theorem CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid
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
    ∃ c : K, f = algebraMap K ↥(holRing ϖ) c := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid.solution
