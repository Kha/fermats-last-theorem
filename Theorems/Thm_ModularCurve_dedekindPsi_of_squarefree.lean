module

public import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_dedekindPsi_of_squarefree

@[expose] public section

open ModularCurve
theorem ModularCurve.dedekindPsi_of_squarefree {N : ℕ} (hN : Squarefree N) : dedekindPsi N = ∏ p ∈ N.primeFactors, (p + 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dedekindPsi_of_squarefree.solution
