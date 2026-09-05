module

public import Definitions.Def_ModularCurve_X0
import P2M.Sol.S_ModularCurve_exists_phiIrreducible_evalSymm
import P2M.Sol.S_ModularCurve_dedekindPsi_prime
import P2M.Util
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace P2MW.S_ModularCurve_finrank_adjoin_jqN_eq_of_prime

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "jq jqN dedekindPsi ModularPolynomialData algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin PhiIrreducible exists_phiIrreducible_evalSymm dedekindPsi_prime"
p2m_open "ModularCurve"

variable {N : ℕ} [NeZero N]

theorem aeval_jqN_toAdjoin (data : ModularPolynomialData N) : Polynomial.aeval (jqN N) data.toAdjoin = 0 := by
  rw [ModularPolynomialData.toAdjoin, Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
  exact data.eval_eq_zero

theorem minpoly_jqN_eq_toAdjoin (data : ModularPolynomialData N) (h : PhiIrreducible data) :
    minpoly ℚ⟮jq⟯ (jqN N) = data.toAdjoin :=
  (minpoly.eq_of_irreducible_of_monic h (aeval_jqN_toAdjoin data) data.toAdjoin_monic).symm

theorem finrank_adjoin_jqN_eq (data : ModularPolynomialData N) (h : PhiIrreducible data) :
    Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN N⟯ = dedekindPsi N := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) := ⟨data.toAdjoin, data.toAdjoin_monic, by
    rw [← Polynomial.aeval_def]; exact aeval_jqN_toAdjoin data⟩
  rw [IntermediateField.adjoin.finrank hint, minpoly_jqN_eq_toAdjoin data h, ModularPolynomialData.toAdjoin,
    data.monic.natDegree_map, data.natDegree_eq]

private theorem finrank_adjoin_jqN_eq_of_prime (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN ℓ⟯ = ℓ + 1 := by
  obtain ⟨data, hirr, -⟩ := exists_phiIrreducible_evalSymm ℓ
  rw [finrank_adjoin_jqN_eq data hirr, dedekindPsi_prime hℓ.out]

end ModularCurve

end

set_option pp.universes true in
#check @ModularCurve.finrank_adjoin_jqN_eq

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_finrank_adjoin_jqN_eq_of_prime.ModularCurve ModularCurve.PhiGen in

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN ℓ} : Set (LaurentSeries ℚ))) = ℓ + 1 :=
  ModularCurve.finrank_adjoin_jqN_eq_of_prime ℓ
end S_ModularCurve_finrank_adjoin_jqN_eq_of_prime
end P2MW

public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
theorem ModularCurve.finrank_adjoin_jqN_eq_of_prime (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN ℓ} : Set (LaurentSeries ℚ))) = ℓ + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqN_eq_of_prime.solution
end
