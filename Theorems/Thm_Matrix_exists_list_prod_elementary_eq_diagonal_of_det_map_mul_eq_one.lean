import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one

set_option autoImplicit false

theorem Matrix.exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one
    {A : Type*} [Ring A] {F : Type*} [Field F]
    (φ : A ≃+* Matrix (Fin 2) (Fin 2) F) (g₁ g₂ : Aˣ) (h : (φ ((g₁ : A) * g₂)).det = 1) :
    ∃ l : List (Bool × A),
      (l.map fun p : Bool × A =>
        if p.1 then !![(1 : A), p.2; 0, 1] else !![(1 : A), 0; p.2, 1]).prod = !![(g₁ : A), 0; 0, (g₂ : A)] := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one.solution
