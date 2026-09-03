import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower
attribute [-instance] ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_fin_mul_forall_exists_finprod_smul_eq_of_tower
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [IsGalois E L] [IsGalois L F]
    (w : HeightOneSpectrum (𝓞 F))
    (h : HeightOneSpectrum.under (𝓞 E) w =
      HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w))
    (n : ℕ) (c : Fin n → ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ)
    (hc : ∀ a : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
      ∃ (i : Fin n) (b : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ),
        (((∏ᶠ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • b :
            ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) :
            ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom E L
            (⟨HeightOneSpectrum.under (𝓞 L) w, rfl⟩ :
              (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 L))
            ((a * (c i)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) :
              (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E))
    (m : ℕ) (d : Fin m → ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ)
    (hd : ∀ a' : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ,
      ∃ (j : Fin m) (b : (w.adicCompletion F)ˣ),
        (((∏ᶠ τ : ↥(NumberField.PlaceDecomp.decomp L F w), τ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom L F
            (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))
            ((a' * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) :
              (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) :
    ∃ c' : Fin (n * m) → ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
      ∀ a : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
        ∃ (k : Fin (n * m)) (b : (w.adicCompletion F)ˣ),
          (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
              w.adicCompletion F) =
            HeightOneSpectrum.Extension.adicCompletionSemialgHom E F
              (⟨w, h⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 F))
              ((a * (c' k)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) :
                (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower.solution
