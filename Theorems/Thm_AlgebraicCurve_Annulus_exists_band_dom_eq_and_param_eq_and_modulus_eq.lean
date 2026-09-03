import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_exists_band_dom_eq_and_param_eq_and_modulus_eq
attribute [-instance] AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.exists_band_dom_eq_and_param_eq_and_modulus_eq
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    (An : Annulus A F) (b c : L) (t : A)
    (hc : A.valuation c ≤ 1) (hc0 : c ≠ 0) (ht : t ∈ IsLocalRing.maximalIdeal A) (ht0 : (t : L) ≠ 0)
    (hb : A.valuation (c * (t : L)) = A.valuation b)
    (hmod : A.valuation ((An.modulus : A) : L) ≤ A.valuation (c * (t : L))) :
    ∃ B : Annulus A F,
      B.dom = {P | P ∈ An.dom ∧ A.valuation b < A.valuation (P.evalAt An.param) ∧
        A.valuation (P.evalAt An.param) < A.valuation c} ∧
      B.param = (algebraMap L F c)⁻¹ * An.param ∧
      B.modulus = t := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_exists_band_dom_eq_and_param_eq_and_modulus_eq.solution
