import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinTwoSlash_slash_eq_self

open scoped ModularForm

theorem ModularCurve.eisensteinTwoSlash_slash_eq_self (p : ℕ) [NeZero p] : ∀ γ ∈ ((CongruenceSubgroup.Gamma0 p : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), (EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ = EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinTwoSlash_slash_eq_self.solution
