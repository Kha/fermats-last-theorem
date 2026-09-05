module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_phiIrreducible_of_prime

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.phiIrreducible_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) : PhiIrreducible data := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_phiIrreducible_of_prime.solution
