import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_sum_apply_conj_single_eq_sum_apply_single

set_option autoImplicit false

theorem Matrix.sum_apply_conj_single_eq_sum_apply_single
    {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (C : Matrix (Fin 3) (Fin 3) K) (hC : C.det ≠ 0)
    (β : Matrix (Fin 3) (Fin 3) K →ₗ[K] Matrix (Fin 3) (Fin 3) K →ₗ[K] V)
    (τ : Matrix (Fin 3) (Fin 3) K →ₗ[K] Matrix (Fin 3) (Fin 3) K →ₗ[K] Matrix (Fin 3) (Fin 3) K →ₗ[K] V) :
    (∑ i : Fin 3, ∑ j : Fin 3, β (C * Matrix.single i j 1 * C⁻¹) (C * Matrix.single j i 1 * C⁻¹)
      = ∑ i : Fin 3, ∑ j : Fin 3, β (Matrix.single i j 1) (Matrix.single j i 1)) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        τ (C * Matrix.single i j 1 * C⁻¹) (C * Matrix.single j k 1 * C⁻¹) (C * Matrix.single k i 1 * C⁻¹)
      = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        τ (Matrix.single i j 1) (Matrix.single j k 1) (Matrix.single k i 1)) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_sum_apply_conj_single_eq_sum_apply_single.solution
