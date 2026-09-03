import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import P2M.Util
import P2M.Sol.S_Matrix_sub_smul_one_mul_sub_smul_one_eq_zero

theorem Matrix.sub_smul_one_mul_sub_smul_one_eq_zero {A : Type*} [CommRing A]
    {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) :
    (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) * (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_sub_smul_one_mul_sub_smul_one_eq_zero.solution
