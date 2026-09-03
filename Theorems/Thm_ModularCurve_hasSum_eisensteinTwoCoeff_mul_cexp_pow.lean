import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_eisensteinTwoCoeff_mul_cexp_pow

theorem ModularCurve.hasSum_eisensteinTwoCoeff_mul_cexp_pow (p : ℕ) [NeZero p] (τ : UpperHalfPlane) : HasSum (fun n : ℕ => (ModularCurve.eisensteinTwoCoeff p n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n) ((p : ℂ) * EisensteinSeries.E2 (ModularForm.heckeDiagMatrix p • τ) - EisensteinSeries.E2 τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_eisensteinTwoCoeff_mul_cexp_pow.solution
