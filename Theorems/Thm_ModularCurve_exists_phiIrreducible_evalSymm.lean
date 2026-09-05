module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_phiIrreducible_evalSymm

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.exists_phiIrreducible_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_phiIrreducible_evalSymm.solution
