module

public import Definitions.Def_ModularCurve_X0
public import P2M.Util
public import P2M.Sol.S_ModularCurve_one_le_coeff_jq

@[expose] public section

open ModularCurve
theorem ModularCurve.one_le_coeff_jq (n : ℕ) : (1 : ℚ) ≤ jq.coeff (n : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_one_le_coeff_jq.solution
