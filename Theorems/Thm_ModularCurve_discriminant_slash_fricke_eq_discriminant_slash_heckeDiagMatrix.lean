import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import P2M.Util
import P2M.Sol.S_ModularCurve_discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix

open scoped ModularForm

theorem ModularCurve.discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix (p : ℕ) [NeZero p] (W : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) : ModularForm.discriminant ∣[(12 : ℤ)] W = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix.solution
