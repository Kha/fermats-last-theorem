module

public import Definitions.Def_ModularCurve_X0
import P2M.Util
import Definitions.Def_ModularCurve_PhiGen

namespace P2MW.S_ModularCurve_aeval_jqN_toAdjoin

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "jq jqN dedekindPsi ModularPolynomialData algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin PhiIrreducible"
p2m_open "ModularCurve"

variable {N : ℕ} [NeZero N]

private theorem aeval_jqN_toAdjoin (data : ModularPolynomialData N) : Polynomial.aeval (jqN N) data.toAdjoin = 0 := by
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

end ModularCurve

end

set_option pp.universes true in
#check @ModularCurve.finrank_adjoin_jqN_eq

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_aeval_jqN_toAdjoin.ModularCurve ModularCurve.PhiGen in

theorem solution {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : Polynomial.aeval (jqN N) data.toAdjoin = 0 :=
  ModularCurve.aeval_jqN_toAdjoin data
end S_ModularCurve_aeval_jqN_toAdjoin
end P2MW

public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
theorem ModularCurve.aeval_jqN_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : Polynomial.aeval (jqN N) data.toAdjoin = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_aeval_jqN_toAdjoin.solution
end
