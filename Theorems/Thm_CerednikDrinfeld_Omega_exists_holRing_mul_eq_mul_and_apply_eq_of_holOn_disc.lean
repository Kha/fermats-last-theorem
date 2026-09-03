import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc
attribute [-simp] CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Omega
theorem CerednikDrinfeld.Omega.exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (A B : ↥(Omega.holRing ϖ)) (hB : B ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ K)) (N : ℕ)
    (hD : {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} ⊆ Omega.upperHalfPlane K₀ K)
    (a b : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} → K)
    (ha : a ∈ Omega.holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}) (hb : b ∈ Omega.holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N})
    (hbz : ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, (w : K) = (z : K) → b w ≠ 0)
    (heq : ∃ Z : Set ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, Z.Finite ∧ ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, w ∉ Z →
      (B : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * a w = (A : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * b w) :
    ∃ G H : ↥(Omega.holRing ϖ), (H : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ A * H = B * G ∧
      ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, (w : K) = (z : K) →
        (G : ↥(Omega.upperHalfPlane K₀ K) → K) z * b w = (H : ↥(Omega.upperHalfPlane K₀ K) → K) z * a w := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc.solution
