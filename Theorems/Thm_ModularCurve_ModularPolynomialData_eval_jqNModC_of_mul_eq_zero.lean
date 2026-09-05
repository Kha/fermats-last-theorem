module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_JqCoeff
public import Definitions.Def_ModularCurve_PhiGen
public import P2M.Util
public import P2M.Sol.S_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero

@[expose] public section

theorem ModularCurve.ModularPolynomialData.eval_jqNModC_of_mul_eq_zero {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (hsymm : ModularCurve.EvalSymm data.Φ) (K : Type*) [CommRing K] (d : ℕ) [NeZero d] : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jqNModC K (d * ℓ))).toRingHom (ModularCurve.jqNModC K d) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero.solution
