import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import P2M.Util
import P2M.Sol.S_Matrix_specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag

set_option autoImplicit false

theorem Matrix.specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag
    (k : Matrix (Fin 2) (Fin 2) ℂ) (hk : k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ a b c : ℝ,
      k = !![Complex.exp (a * Complex.I), 0; 0, Complex.exp (-(a * Complex.I))] *
            !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)] *
            !![Complex.exp (c * Complex.I), 0; 0, Complex.exp (-(c * Complex.I))] := by p2m_exact_reverting @_root_.P2MW.S_Matrix_specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag.solution
