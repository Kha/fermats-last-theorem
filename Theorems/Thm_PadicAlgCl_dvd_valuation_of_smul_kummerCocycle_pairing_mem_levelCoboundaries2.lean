import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_PadicAlgCl_dvd_valuation_of_smul_kummerCocycle_pairing_mem_levelCoboundaries2
attribute [-instance] ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal
attribute [-simp] ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π IsLocalRing.principalUnits_zero

set_option autoImplicit false
theorem PadicAlgCl.dvd_valuation_of_smul_kummerCocycle_pairing_mem_levelCoboundaries2
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℤ) (hχlc : groupCohomology.IsLevelConstant₁ (localGaloisToGlobal p) χ)
    (hχ : ∀ σ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))
    (hKχ : ∀ σ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → σ w = w) ↔ (p : ℤ) ∣ χ σ)
    (φ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (hφ : ∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → φ w = w ^ p)
    (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ)
    (hα : algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p)
    (hcob : (fun g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) × (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) =>
        (MonoidHom.toAdditive (rootsOfUnity p (PadicAlgCl p)).subtype).toIntLinearMap
          ((χ g.1) • (groupCohomology.Kummer.kummerRep ℚ_[p] (PadicAlgCl p) p).ρ g.1
            (Additive.ofMul (groupCohomology.Kummer.kummerCocycleRoots hα g.2))))
      ∈ groupCohomology.levelCoboundaries₂ (localGaloisToGlobal p)
          (Rep.ofAlgebraAutOnUnits ℚ_[p] (PadicAlgCl p))) :
    (p : ℤ) ∣ Padic.valuation (a : ℚ_[p]) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_dvd_valuation_of_smul_kummerCocycle_pairing_mem_levelCoboundaries2.solution
