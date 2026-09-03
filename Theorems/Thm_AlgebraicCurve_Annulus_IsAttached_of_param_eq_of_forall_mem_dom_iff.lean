import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_IsAttached_of_param_eq_of_forall_mem_dom_iff
attribute [-instance] AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.IsAttached.of_param_eq_of_forall_mem_dom_iff
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField ↥A) Fb]
    (An₀ : Annulus A F) (C : ComponentChart A F Fb) (x : Place (IsLocalRing.ResidueField ↥A) Fb)
    (hatt : An₀.IsAttached C x)
    (B : Annulus A F) (hparam : B.param = An₀.param)
    (b : L) (hdom : ∀ P, P ∈ B.dom ↔ P ∈ An₀.dom ∧ A.valuation b < A.valuation (P.evalAt An₀.param)) :
    B.IsAttached C x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_IsAttached_of_param_eq_of_forall_mem_dom_iff.solution
