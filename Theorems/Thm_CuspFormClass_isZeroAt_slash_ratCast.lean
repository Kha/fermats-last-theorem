import Mathlib
import P2M.Util
import P2M.Sol.S_CuspFormClass_isZeroAt_slash_ratCast
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem CuspFormClass.isZeroAt_slash_ratCast {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : OnePoint.IsZeroAt c (SlashAction.map k (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g) ⇑f) k := by p2m_exact_reverting @_root_.P2MW.S_CuspFormClass_isZeroAt_slash_ratCast.solution
