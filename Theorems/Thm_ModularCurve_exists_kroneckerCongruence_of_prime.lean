module

public import Mathlib
public import Definitions.Def_ModularCurve_KroneckerTransport
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_kroneckerCongruence_of_prime

@[expose] public section

theorem ModularCurve.exists_kroneckerCongruence_of_prime (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ data : ModularCurve.ModularPolynomialData ℓ, ModularCurve.KroneckerCongruence ℓ data := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_kroneckerCongruence_of_prime.solution
