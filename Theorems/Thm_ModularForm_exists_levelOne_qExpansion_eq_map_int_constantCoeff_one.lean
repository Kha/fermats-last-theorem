import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one

set_option autoImplicit false

open scoped MatrixGroups in

theorem ModularForm.exists_levelOne_qExpansion_eq_map_int_constantCoeff_one (a b : ℕ) (e : ℤ)
    (he : 4 * (a : ℤ) + 6 * (b : ℤ) = e) :
    ∃ (E : ModularForm 𝒮ℒ e) (P : PowerSeries ℤ),
      P.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ) ∧
      PowerSeries.constantCoeff P = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one.solution
