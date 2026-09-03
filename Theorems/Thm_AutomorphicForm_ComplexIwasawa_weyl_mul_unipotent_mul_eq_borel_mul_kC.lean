import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC

open ComplexConjugate AutomorphicForm.ComplexIwasawa

theorem AutomorphicForm.ComplexIwasawa.weyl_mul_unipotent_mul_eq_borel_mul_kC
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    !![(0 : ℂ), 1; 1, 0] * !![1, z; 0, 1] * g
      = !![-g.det / (radC g z : ℂ),
            (g 1 0 * conj (botP g z) + g 1 1 * conj (botQ g z)) / (radC g z : ℂ);
           0, (radC g z : ℂ)] * kC g z := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC.solution
