module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Sol.S_ModularCurve_exists_isFrickeAut_of_modularPolynomialData
import P2M.Sol.S_ModularCurve_exists_phiIrreducible_evalSymm
import P2M.Util
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace P2MW.S_ModularCurve_exists_isFrickeAut

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionField ℓ ≃ₐ[ℚ] modularFunctionField ℓ, IsFrickeAut ℓ σ := by
  obtain ⟨data, hirr, hsymm⟩ := ModularCurve.exists_phiIrreducible_evalSymm ℓ
  exact ModularCurve.exists_isFrickeAut_of_modularPolynomialData data hsymm hirr

end
end S_ModularCurve_exists_isFrickeAut
end P2MW

public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.exists_isFrickeAut (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionField ℓ ≃ₐ[ℚ] modularFunctionField ℓ, IsFrickeAut ℓ σ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isFrickeAut.solution
end
