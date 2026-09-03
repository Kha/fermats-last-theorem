import Definitions.Def_CerednikDrinfeld_OmegaTubes
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~exists_eq_mul_prod_zpow_mul_one_add_of_isUnit"

theorem CerednikDrinfeld.Omega.v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) (c : Γ₀) (m : ℤ)
    (hcm : ∀ (z : K) (hz : z ∈ stdEdgeTube ϖ), Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) = c * Valued.v z ^ m) :
    (∀ w : ↥(upperHalfPlane K₀ K), (w : K) ∈ affinoid ϖ 0 → Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) w) = c) ∧
    (∀ w : ↥(upperHalfPlane K₀ K), (algebraMap K₀ K ϖ.ϖ)⁻¹ * (w : K) ∈ affinoid ϖ 0 →
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) w) = c * Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube.solution
