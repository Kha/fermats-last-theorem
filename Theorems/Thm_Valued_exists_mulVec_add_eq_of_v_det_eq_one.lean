import Mathlib
import P2M.Util
import P2M.Sol.S_Valued_exists_mulVec_add_eq_of_v_det_eq_one

set_option autoImplicit false

theorem Valued.exists_mulVec_add_eq_of_v_det_eq_one
    {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ m : ℕ, Valued.v x ^ m ≤ Valued.v y)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j : Fin n, Valued.v (A i j) ≤ 1)
    (hdet : Valued.v A.det = 1)
    (R : (Fin n → K) → (Fin n → K)) (hR0 : R 0 = 0)
    (hR : ∀ (ε ε' : Fin n → K) (s t : Γ₀), s < 1 → (∀ j, Valued.v (ε j) ≤ s) → (∀ j, Valued.v (ε' j) ≤ s) →
      (∀ j, Valued.v (ε j - ε' j) ≤ t) → ∀ i, Valued.v (R ε i - R ε' i) ≤ t * s)
    (y : Fin n → K) (s : Γ₀) (hs : s < 1) (hy : ∀ i, Valued.v (y i) ≤ s) :
    ∃ ε : Fin n → K, (∀ i, Valued.v (ε i) ≤ s) ∧ A.mulVec ε + R ε = y := by p2m_exact_reverting @_root_.P2MW.S_Valued_exists_mulVec_add_eq_of_v_det_eq_one.solution
