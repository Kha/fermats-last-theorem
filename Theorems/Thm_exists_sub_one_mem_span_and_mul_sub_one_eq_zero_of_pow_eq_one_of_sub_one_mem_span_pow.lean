import Mathlib
import P2M.Util
import P2M.Sol.S_exists_sub_one_mem_span_and_mul_sub_one_eq_zero_of_pow_eq_one_of_sub_one_mem_span_pow

theorem exists_sub_one_mem_span_and_mul_sub_one_eq_zero_of_pow_eq_one_of_sub_one_mem_span_pow
    (p : ℕ) (hp : p.Prime) (q : ℕ) (hq : q ≠ 0)
    (T : Type*) [CommRing T] (htf : ∀ x : T, (p : T) * x = 0 → x = 0)
    (u : T) (hu : u ^ q = 1)
    (hN : u - 1 ∈ Ideal.span {((p : T) ^ (padicValNat p q + 1))}) :
    ∃ a : T, a - 1 ∈ Ideal.span {(p : T)} ∧ a * (u - 1) = 0 := by p2m_exact_reverting @_root_.P2MW.S_exists_sub_one_mem_span_and_mul_sub_one_eq_zero_of_pow_eq_one_of_sub_one_mem_span_pow.solution
