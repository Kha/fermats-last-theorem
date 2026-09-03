import Definitions.Def_CerednikDrinfeld_OmegaTubes
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) :
    ∃ (c : Γ₀) (m : ℤ), ∀ (z : K) (hz : z ∈ stdEdgeTube ϖ),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) = c * Valued.v z ^ m := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube.solution
