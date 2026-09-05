module

public import Definitions.Def_ModularCurve_KroneckerTransport
import P2M.Util
import P2M.Sol.S_ModularCurve_kroneckerCongruence

@[expose] public section
attribute [-simp] ModularCurve.jqNModC_one

open ModularCurve
theorem ModularCurve.kroneckerCongruence (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (data : ModularPolynomialData ℓ) : KroneckerCongruence ℓ data := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_kroneckerCongruence.solution
