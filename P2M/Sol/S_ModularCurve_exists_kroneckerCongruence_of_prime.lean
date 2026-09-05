module

public import Theorems.Thm_ModularCurve_kroneckerCongruence
public import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_exists_kroneckerCongruence_of_prime

theorem solution (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ data : ModularCurve.ModularPolynomialData ℓ, ModularCurve.KroneckerCongruence ℓ data := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData_of_squarefree ℓ
    (Fact.out : ℓ.Prime).squarefree (Fact.out : ℓ.Prime).one_lt
  exact ⟨data, ModularCurve.kroneckerCongruence ℓ data⟩
