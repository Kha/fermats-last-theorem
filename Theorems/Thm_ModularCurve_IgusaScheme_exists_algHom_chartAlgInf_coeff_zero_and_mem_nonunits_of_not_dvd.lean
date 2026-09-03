import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero
attribute [-simp] ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open Polynomial ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let u : ↥(modularFunctionFieldFull (N * p)) := (jFull (N * p))⁻¹
    let jp : ↥(modularFunctionFieldFull (N * p)) :=
      ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩
    let t : ↥(modularFunctionFieldFull (N * p)) := jp * u ^ p

    (∃ ε : Fin 2 → (↥(chartAlgInf (N * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)]
        ↥(GaloisRep.ratLocalizedAt p)),
      ∀ b : ↥(chartAlgInf (N * p) p),
        ((ε 0 b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
            = ((b : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ).coeff 0 ∧
        ((ε 1 b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
            = ((atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))) :
                ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ).coeff 0) ∧

    (t ∈ chartAlgInf (N * p) p ∧
      (∃ h : Polynomial (Polynomial ℤ), h.Monic ∧
        h.map (Polynomial.evalRingHom 0) = X ^ (p + 1) - X ^ p ∧
        h.eval₂ (Polynomial.eval₂RingHom (algebraMap ℤ ↥(modularFunctionFieldFull (N * p))) u) t
          = 0) ∧
      ((t : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ).coeff 0 = 1 ∧
      ((atkinLehnerInvolutionFull N p t : ↥(modularFunctionFieldFull (N * p))) :
        LaurentSeries ℚ).coeff 0 = 0) ∧

    (∀ W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull (N * p)),
      (∀ f : ↥(modularFunctionFieldFull (N * p)), f ∈ W₀ ↔
        ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y
            = coeffMap (Int.castRingHom ℚ) x) →
      (∀ f : ↥(modularFunctionFieldFull (N * p)), f ∈ W₁ ↔
        atkinLehnerInvolutionFull N p f ∈ W₀) →
      (t - 1 ∈ W₀.nonunits ∧
        ((atkinLehnerInvolutionFull N p (t - 1) : ↥(modularFunctionFieldFull (N * p))) :
          LaurentSeries ℚ).coeff 0 = -1) ∧
      (t ^ p - u ^ (p ^ 2 - 1) ∈ W₁.nonunits ∧
        ((t ^ p - u ^ (p ^ 2 - 1) : ↥(modularFunctionFieldFull (N * p))) :
          LaurentSeries ℚ).coeff 0 = 1)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd.solution
