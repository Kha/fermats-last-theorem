import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one

set_option autoImplicit false

theorem LanglandsTunnell.Artin.eq_one_or_eq_commutator_of_det_eq_one :
    ∀ g : GL (Fin 2) (ZMod 3), (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 →
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
        ∃ x : GL (Fin 2) (ZMod 3), ∃ y : GL (Fin 2) (ZMod 3), g = x * y * x⁻¹ * y⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one.solution
