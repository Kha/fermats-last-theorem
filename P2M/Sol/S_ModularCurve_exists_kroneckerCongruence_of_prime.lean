module

import P2M.Sol.S_ModularCurve_kroneckerCongruence
import P2M.Sol.S_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import P2M.Util
public import Mathlib
public import Definitions.Def_ModularCurve_KroneckerTransport

namespace P2MW.S_ModularCurve_exists_kroneckerCongruence_of_prime

theorem solution (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ data : ModularCurve.ModularPolynomialData ℓ, ModularCurve.KroneckerCongruence ℓ data := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData_of_squarefree ℓ
    (Fact.out : ℓ.Prime).squarefree (Fact.out : ℓ.Prime).one_lt
  exact ⟨data, ModularCurve.kroneckerCongruence ℓ data⟩
end S_ModularCurve_exists_kroneckerCongruence_of_prime
end P2MW

public section
theorem ModularCurve.exists_kroneckerCongruence_of_prime (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ data : ModularCurve.ModularPolynomialData ℓ, ModularCurve.KroneckerCongruence ℓ data := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_kroneckerCongruence_of_prime.solution
end
