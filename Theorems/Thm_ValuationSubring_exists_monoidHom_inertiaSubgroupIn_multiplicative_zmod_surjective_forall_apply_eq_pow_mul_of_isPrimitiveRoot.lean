import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot
attribute [-instance] ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ExtCitation.LocalLevel.coe_smul_OO

set_option autoImplicit false

theorem ValuationSubring.exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot
    {r : ℕ} (hr : r.Prime) {m : ℕ} [NeZero m] (hrm : ¬ r ∣ m)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ m) :
    ∃ t : ↥(A.inertiaSubgroupIn ℚ) →* Multiplicative (ZMod m),
      Function.Surjective t ∧
      ∀ (σ : ↥(A.inertiaSubgroupIn ℚ)) (x : AlgebraicClosure ℚ), x ^ m = (r : AlgebraicClosure ℚ) →
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x = ζ ^ (Multiplicative.toAdd (t σ)).val * x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot.solution
