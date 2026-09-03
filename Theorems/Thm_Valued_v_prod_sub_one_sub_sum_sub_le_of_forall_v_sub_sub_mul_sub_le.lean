import Mathlib
import P2M.Util
import P2M.Sol.S_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le

set_option autoImplicit false

theorem Valued.v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le
    {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {n r : ℕ} (F : Fin n → Fin r → K → K) (d : Fin n → Fin r → K)
    (hd : ∀ i j, Valued.v (d i j) ≤ 1)
    (hF0 : ∀ i j, F i j 0 = 1)
    (hF : ∀ (i : Fin n) (j : Fin r) (e e' : K) (s t : Γ₀), s < 1 → Valued.v e ≤ s → Valued.v e' ≤ s →
      Valued.v (e - e') ≤ t → Valued.v (F i j e - F i j e' - d i j * (e - e')) ≤ t * s) :
    (∀ j : Fin r, (∏ i, F i j ((0 : Fin n → K) i)) - 1 - ∑ i, d i j * (0 : Fin n → K) i = 0) ∧
    ∀ (ε ε' : Fin n → K) (s t : Γ₀), s < 1 → (∀ i, Valued.v (ε i) ≤ s) → (∀ i, Valued.v (ε' i) ≤ s) →
      (∀ i, Valued.v (ε i - ε' i) ≤ t) →
      ∀ j : Fin r, Valued.v (((∏ i, F i j (ε i)) - 1 - ∑ i, d i j * ε i) - ((∏ i, F i j (ε' i)) - 1 - ∑ i, d i j * ε' i))
        ≤ t * s := by p2m_exact_reverting @_root_.P2MW.S_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le.solution
