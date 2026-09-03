import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Matrix.Notation
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_smul_one_add_smul_eq_diagonal_mul_of_mem_Gamma0

set_option autoImplicit false

open Matrix
open scoped MatrixGroups

theorem ModularCurve.exists_smul_one_add_smul_eq_diagonal_mul_of_mem_Gamma0 (M s : ℕ)
    (u : SL(2, ℤ)) (hu : u ∈ CongruenceSubgroup.Gamma0 (M * s))
    (hell : (u : Matrix (Fin 2) (Fin 2) ℤ).trace = 0 ∨ (u : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 ∨
      (u : Matrix (Fin 2) (Fin 2) ℤ).trace = -1) :
    ∃ (x y : ℤ) (δ : SL(2, ℤ)), δ ∈ CongruenceSubgroup.Gamma0 M ∧
      x • (1 : Matrix (Fin 2) (Fin 2) ℤ) + y • (u : Matrix (Fin 2) (Fin 2) ℤ)
        = !![1, 0; 0, (s : ℤ)] * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_smul_one_add_smul_eq_diagonal_mul_of_mem_Gamma0.solution
