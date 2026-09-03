import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) (m : K₀ → ℤ) (mInf : ℤ)
    (hm : ∀ t ∈ T, ∃ c : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t) →
      Valued.v ((z : K) - algebraMap K₀ K t) < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = c * Valued.v ((z : K) - algebraMap K₀ K t) ^ (m t))
    (hmInf : ∃ c : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      Valued.v (algebraMap K₀ K ϖ.ϖ) < (Valued.v (z : K))⁻¹ → (Valued.v (z : K))⁻¹ < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = c * (Valued.v (z : K))⁻¹ ^ mInf) :
    (∑ t ∈ T, m t) + mInf = 0 ∧
    ∃ c₀ : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
      Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) =
          c₀ * ∏ t ∈ T, Valued.v ((z : K) - algebraMap K₀ K t) ^ (m t) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow.solution
