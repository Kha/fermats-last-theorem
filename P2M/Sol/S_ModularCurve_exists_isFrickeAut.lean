module

public import Definitions.Def_ModularCurve_AtkinLehner
public import Theorems.Thm_ModularCurve_exists_isFrickeAut_of_modularPolynomialData
public import Theorems.Thm_ModularCurve_exists_phiIrreducible_evalSymm
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_exists_isFrickeAut

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionField ℓ ≃ₐ[ℚ] modularFunctionField ℓ, IsFrickeAut ℓ σ := by
  obtain ⟨data, hirr, hsymm⟩ := ModularCurve.exists_phiIrreducible_evalSymm ℓ
  exact ModularCurve.exists_isFrickeAut_of_modularPolynomialData data hsymm hirr

end
