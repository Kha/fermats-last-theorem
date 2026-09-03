import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle
attribute [-instance] ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal
attribute [-simp] groupCohomology.continuousH2ToH2_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π IsLocalRing.principalUnits_zero

set_option autoImplicit false
theorem GaloisRepAdic.exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic B) (hdet : ρ.DetIsCyclotomic p)
    (b : Module.Basis (Fin 2) B ρ.V)
    (hLD : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ B ∙ b 0)
    (hLI : ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ B ∙ b 0)
    (t : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0)
    (hsq : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∀ z : B,
      (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ B ∙ b 0) → z * z - 1 ∈ Ideal.span {t})
    (hne : ∃ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∃ z : B,
      (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ B ∙ b 0) ∧ z * z ≠ 1) :
    ∃ β : PadicAlgCl p, β ^ p = 1 + (p : PadicAlgCl p) ∧
      ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ξ : PadicAlgCl p, ξ ^ p = 1 → τ ξ = ξ) → τ β = β →
          ∀ v : ρ.V, ρ.ρ (localGaloisToGlobal p τ) v - v ∈
            (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B ρ.V) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle.solution
