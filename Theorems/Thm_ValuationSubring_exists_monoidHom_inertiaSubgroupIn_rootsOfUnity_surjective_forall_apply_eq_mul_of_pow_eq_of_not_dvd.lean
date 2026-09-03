import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_rootsOfUnity_surjective_forall_apply_eq_mul_of_pow_eq_of_not_dvd
attribute [-instance] ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ExtCitation.LocalLevel.coe_smul_OO

set_option autoImplicit false

theorem ValuationSubring.exists_monoidHom_inertiaSubgroupIn_rootsOfUnity_surjective_forall_apply_eq_mul_of_pow_eq_of_not_dvd
    {r : ℕ} (hr : r.Prime) {m : ℕ} (hrm : ¬ r ∣ m)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ t : ↥(A.inertiaSubgroupIn ℚ) →* ↥(rootsOfUnity m (AlgebraicClosure ℚ)),
      Function.Surjective t ∧
      ∀ (σ : ↥(A.inertiaSubgroupIn ℚ)) (x : AlgebraicClosure ℚ), x ^ m = (r : AlgebraicClosure ℚ) →
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x = ((t σ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) * x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_rootsOfUnity_surjective_forall_apply_eq_mul_of_pow_eq_of_not_dvd.solution
