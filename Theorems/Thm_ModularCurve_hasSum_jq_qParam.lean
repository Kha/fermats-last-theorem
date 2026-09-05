module

public import Definitions.Def_ModularCurve_X0
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_jq_qParam

@[expose] public section

theorem ModularCurve.hasSum_jq_qParam (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((ModularCurve.jq.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_jq_qParam.solution
