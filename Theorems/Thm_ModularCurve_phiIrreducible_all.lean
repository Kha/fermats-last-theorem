module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_phiIrreducible_all

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.phiIrreducible_all (N : ℕ) [NeZero N] (data : ModularPolynomialData N) : PhiIrreducible data := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_phiIrreducible_all.solution
