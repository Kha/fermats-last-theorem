import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
attribute [-instance] ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ
attribute [-simp] TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one
attribute [-simp] WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in

theorem ModularCurve.residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hp : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hmem : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (N * p))
    (R₀ : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar (N * p))
      (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))

    (h₀ : ∀ (y : LaurentSeries A)
      (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar (N * p)),
      ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
          ModularCurve.modularFunctionFieldBar (N * p)) ∈ R₀.integers,
        (((R₀.residue ⟨_, hint⟩ :
            ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
            LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.coeffMap (IsLocalRing.residue A) y)
    [DecidableEq (IsLocalRing.ResidueField A)] (S₀ : Finset (IsLocalRing.ResidueField A))
    (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ModularCurve.ssJSet p (IsLocalRing.ResidueField A)) :
    ∃ hu₀ : (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.modularUnitSeries p),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ :
          ModularCurve.modularFunctionFieldBar (N * p)) ∈ R₀.integers,
      (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.modularUnitSeries p),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ :
          ModularCurve.modularFunctionFieldBar (N * p))⁻¹ ∈ R₀.integers ∧
      (((R₀.residue ⟨_, hu₀⟩ :
          ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        ∏ a ∈ S₀, (ModularCurve.jqModC (IsLocalRing.ResidueField A) - HahnSeries.C a) ^
          (12 / ModularCurve.jWidth a) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation.solution
