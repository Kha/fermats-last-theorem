import Mathlib
import P2M.Util
import P2M.Sol.S_Valued_exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one

set_option autoImplicit false

theorem Valued.exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    {ι : Type} [Fintype ι] (t : ι → K)
    (ht : ∀ a : ι, Valued.v (t a) ≤ 1) (htsep : ∀ a a' : ι, a ≠ a' → 1 ≤ Valued.v (t a - t a'))
    {r : ℕ} (m : Fin r → Fin r → ι → ℤ) (a₀ : Fin r → ι)
    (hdet : Valued.v (Matrix.of (fun i j : Fin r => ((m i j (a₀ i) : ℤ) : K))).det = 1)
    (S : Fin r → Finset K) :
    ∃ b : Fin r → K,
      (∀ i, Valued.v (b i) ≤ 1) ∧
      (∀ i a, Valued.v (b i - t a) = 1) ∧
      (∀ i, ∀ s ∈ S i, 1 ≤ Valued.v (b i - s)) ∧
      ∀ d : Matrix (Fin r) (Fin r) K,
        (∀ i j, Valued.v (d i j - ∑ a, (m i j a : K) / (b i - t a)) < 1) →
        Valued.v d.det = 1 := by p2m_exact_reverting @_root_.P2MW.S_Valued_exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one.solution
