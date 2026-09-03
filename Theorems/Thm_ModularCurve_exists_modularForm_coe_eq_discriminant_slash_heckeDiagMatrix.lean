import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix

open scoped ModularForm

theorem ModularCurve.exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix (p : ℕ) [NeZero p] : ∃ D : ModularForm (CongruenceSubgroup.Gamma0 p) 12, ⇑D = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix.solution
