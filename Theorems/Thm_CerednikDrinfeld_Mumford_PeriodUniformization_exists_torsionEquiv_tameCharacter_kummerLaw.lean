import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_PeriodUniformization_exists_torsionEquiv_tameCharacter_kummerLaw
import Definitions.Def_Compat_Mathlib430
attribute [-instance] ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj ExtCitation.LocalLevel.coe_smul_OO

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford ModularCurve

theorem CerednikDrinfeld.Mumford.PeriodUniformization.exists_torsionEquiv_tameCharacter_kummerLaw
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} {H : HeckeData D}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
    {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}
    (𝒰 : PeriodUniformization r D H A hA T hecke gal)
    (ζ : (A.valuation.Completion)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ χ : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)) ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p),
      (∀ (v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
        Additive.toMul ((((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints) z)) = ζ ^ (χ v z).val) ∧
      ∃ tame : ↥(A.inertiaSubgroupIn ℚ) →* Multiplicative (ZMod p), Function.Surjective tame ∧
        ∀ (σ : ↥(A.inertiaSubgroupIn ℚ)) (u : ↥𝒰.P.U) (x : ↥(ribbonKernel D)),
          (p : ℤ) • (u : 𝒰.P.TorusPoints) = 𝒰.P.QL x →
            ∃ v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)),
              gal (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (𝒰.e u) = 𝒰.e u + 𝒰.e (v : ↥𝒰.P.U) ∧
                χ v = (Multiplicative.toAdd (tame σ)) • ribbonGramModP p D x := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_exists_torsionEquiv_tameCharacter_kummerLaw.solution
