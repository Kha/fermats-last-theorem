import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_mul_apply_eq_of_forall_finite_mul_eq_of_holOn_disc

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~restrict_mem_holOn_of_subset~finite_setOf_apply_eq_zero_disc_of_mem_holOn"

theorem CerednikDrinfeld.Omega.mul_apply_eq_of_forall_finite_mul_eq_of_holOn_disc
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (F : ↥(upperHalfPlane K₀ K) → K) (Φ H : ↥(holRing ϖ))
    (hHF : ∀ n : ℕ, ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧ ∀ z : ↥(affinoid ϖ n), z ∉ Z →
      (H : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ *
          F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ =
        (Φ : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩)
    (z : ↥(upperHalfPlane K₀ K)) (N : ℕ)
    (hD : {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} ⊆ upperHalfPlane K₀ K)
    (a b : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} → K)
    (ha : a ∈ holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N})
    (hb : b ∈ holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N})
    (hbz : ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, (w : K) = (z : K) → b w ≠ 0)
    (hab : ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, b w * F ⟨(w : K), hD w.2⟩ = a w) :
    (H : ↥(upperHalfPlane K₀ K) → K) z * F z = (Φ : ↥(upperHalfPlane K₀ K) → K) z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_mul_apply_eq_of_forall_finite_mul_eq_of_holOn_disc.solution
