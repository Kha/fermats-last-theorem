module

public import Definitions.Def_ModularCurve_X0
public import P2M.Util
public import P2M.Sol.S_ModularCurve_ModularPolynomialData_isIntegral_jqN

@[expose] public section

open ModularCurve IntermediateField
theorem ModularCurve.ModularPolynomialData.isIntegral_jqN {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : IsIntegral ℚ⟮jq⟯ (jqN N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_isIntegral_jqN.solution
