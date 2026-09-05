module

public import Definitions.Def_ModularCurve_X0
public import P2M.Util
public import P2M.Sol.S_ModularCurve_functionFieldGeneration_of_prime

@[expose] public section

open ModularCurve IntermediateField
theorem ModularCurve.functionFieldGeneration_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : FunctionFieldGeneration ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_functionFieldGeneration_of_prime.solution
