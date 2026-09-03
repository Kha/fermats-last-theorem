import Mathlib
import P2M.Util
import P2M.Sol.S_Finset_sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum

set_option autoImplicit false

universe u v

open Classical in

theorem Finset.sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum
    {ι : Type u} [Fintype ι] [LinearOrder ι] {β : Type v} (T : Finset β) (a : β → ℤ)
    (mem : ι → β → Prop) (hcov : ∀ y ∈ T, ∃ i, mem i y) (N : ℕ) (hN : Fintype.card ι ≤ N) :
    ∑ p ∈ Finset.range N, (-1 : ℤ) ^ p *
        ∑ s : {s : Fin (p + 1) → ι // StrictMono s}, ∑ y ∈ T, (if ∀ j, mem (s.1 j) y then a y else 0) =
      ∑ y ∈ T, a y := by p2m_exact_reverting @_root_.P2MW.S_Finset_sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum.solution
