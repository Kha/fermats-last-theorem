import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.ZMod.Basic
import P2M.Util
namespace P2MW.S_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one

set_option autoImplicit false

theorem solution :
    ∀ g : GL (Fin 2) (ZMod 3), (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 →
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
        ∃ x : GL (Fin 2) (ZMod 3), ∃ y : GL (Fin 2) (ZMod 3), g = x * y * x⁻¹ * y⁻¹ := by
  decide +kernel
