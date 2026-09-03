import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real

set_option autoImplicit false

open Matrix

theorem LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real :
    ∃ c C : ℝ, 0 < c ∧ ∀ M : GL (Fin 3) ℝ,
      ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) ℝ),
        Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ * M = n * t * k ∧
        (∀ i j : Fin 3,
          (n : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 ∧ (j < i → (n : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
          ‖(n : Matrix (Fin 3) (Fin 3) ℝ) i j‖ ≤ C) ∧
        (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
        (∀ i : Fin 3, 0 < (t : Matrix (Fin 3) (Fin 3) ℝ) i i) ∧
        c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 0 0 / (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 ∧
        c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 / (t : Matrix (Fin 3) (Fin 3) ℝ) 2 2 ∧
        (k : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real.solution
