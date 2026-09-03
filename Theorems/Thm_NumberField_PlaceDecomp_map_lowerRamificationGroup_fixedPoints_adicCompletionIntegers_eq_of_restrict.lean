import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict
attribute [-instance] ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
p2m_open "scoped NumberField.PlaceDecomp~exists_restrict_decomp_surjective_of_tower~forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"

theorem NumberField.PlaceDecomp.map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F))
    (r : ↥(NumberField.PlaceDecomp.decomp E F w) →* ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L))))
    (hsurj : Function.Surjective r)
    (hr : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E F w),
      ((r σ : ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L)))) : L ≃ₐ[E] L) =
        AlgEquiv.restrictNormalHom L (σ : F ≃ₐ[E] F))
    (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup
        ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥r.ker)
        (↥(NumberField.PlaceDecomp.decomp E F w) ⧸ r.ker) i).map
      (QuotientGroup.quotientKerEquivOfSurjective r hsurj).toMonoidHom =
    IsLocalRing.lowerRamificationGroup ↥((w.under (𝓞 L)).adicCompletionIntegers L)
      ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L))) i := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict.solution
