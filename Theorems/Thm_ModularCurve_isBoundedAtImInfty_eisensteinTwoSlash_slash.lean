import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import P2M.Util
import P2M.Sol.S_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash

open scoped ModularForm

theorem ModularCurve.isBoundedAtImInfty_eisensteinTwoSlash_slash (p : ℕ) [NeZero p] : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, UpperHalfPlane.IsBoundedAtImInfty ((EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash.solution
