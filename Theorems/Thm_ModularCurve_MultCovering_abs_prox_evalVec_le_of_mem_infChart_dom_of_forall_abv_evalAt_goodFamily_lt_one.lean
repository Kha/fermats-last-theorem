import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)

    (hint : ∀ i, goodFamily Φ i ∈ (infChart Γ).integers)
    (cQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → Fin r)
    (hrat : ∀ P ∈ (infChart Γ).dom, P.IsRational)
    (hratio : ∀ P ∈ (infChart Γ).dom, ∀ j, goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ (infChart Γ).integers)
    (hreg : ∀ P ∈ (infChart Γ).dom, ∀ j, goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (hhasse : ∀ P ∈ (infChart Γ).dom, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧
      μ (P.evalAt (goodFamily Φ l * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹)) = 1) :
    ∀ P ∈ (infChart Γ).dom, ∀ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      Q.IsRational →
      (∀ l : Fin r, 1 ≤ (l : ℕ) → goodFamily Φ l ∈ Q.toValuationSubring ∧ μ (Q.evalAt (goodFamily Φ l)) < 1) →
      (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
      |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one.solution
