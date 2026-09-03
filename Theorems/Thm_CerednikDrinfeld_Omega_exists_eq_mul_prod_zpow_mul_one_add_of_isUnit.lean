import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_eq_mul_prod_zpow_mul_one_add_of_isUnit

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_eq_mul_prod_zpow_mul_one_add_of_isUnit
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) :
    ∃ (c : K) (m : K₀ → ℤ) (h : ↥(holRing ϖ)), c ≠ 0 ∧
      (∀ z : ↥(upperHalfPlane K₀ K),
        (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
        Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
          (f : ↥(upperHalfPlane K₀ K) → K) z =
              c * (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) * (1 + (h : ↥(upperHalfPlane K₀ K) → K) z) ∧
          Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) z) < 1) ∧
      ∀ ρ : Γ₀, Valued.v (algebraMap K₀ K ϖ.ϖ) < ρ → ρ ≤ 1 →
        ∃ δ : Γ₀, δ < 1 ∧ ∀ z : ↥(upperHalfPlane K₀ K),
          (∀ t ∈ T, ρ ≤ Valued.v ((z : K) - algebraMap K₀ K t)) → Valued.v (z : K) ≤ ρ⁻¹ →
            Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) z) ≤ δ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_eq_mul_prod_zpow_mul_one_add_of_isUnit.solution
