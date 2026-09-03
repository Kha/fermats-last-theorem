import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization
import Definitions.Def_Compat_Mathlib430
attribute [-instance] ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj ExtCitation.LocalLevel.coe_smul_OO

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford ModularCurve

theorem CerednikDrinfeld.Mumford.nonempty_toricUniformization_of_periodUniformization
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} {H : HeckeData D}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    (hC : ∀ n : ℕ, 0 < n → ∀ c : (A.valuation.Completion)ˣ, ∃ c' : (A.valuation.Completion)ˣ, c' ^ n = c)
    {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
    {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}
    (PU : PeriodUniformization r D H A hA T hecke gal) :
    Nonempty (ToricUniformization p r D H A hA T hecke gal) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_nonempty_toricUniformization_of_periodUniformization.solution
