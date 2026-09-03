import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem

set_option autoImplicit false

universe u
theorem Matrix.apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem {A : Type u} [CommRing A] [IsLocalRing A]
    (hH : ∀ x : A, (∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal A ^ n) → x = 0)
    {a d : A} {q : ℕ} (had : IsUnit (a - (q : A) * d)) (hda : IsUnit (d - (q : A) * a))
    {N : Matrix (Fin 2) (Fin 2) A} (hN : ∀ i j, N i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A)
    (hrel : Matrix.diagonal ![a, d] * N = N ^ q * Matrix.diagonal ![a, d]) :
    N 0 1 = 0 ∧ N 1 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem.solution
