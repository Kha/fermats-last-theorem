import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_exists_pow_dvd_natCard_inf_decomp_smul_of_isPGroup_of_not_dvd_index
attribute [-instance] ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP
attribute [-simp] NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk NumberField.SUnits.val_zsmul NumberField.SUnits.val_add ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open IsDedekindDomain NumberField
p2m_open "scoped NumberField.PlaceDecomp NumberField.PlaceTransport~stabilizer_eq_decomp Pointwise"

theorem NumberField.PlaceTransport.exists_pow_dvd_natCard_inf_decomp_smul_of_isPGroup_of_not_dvd_index
    (p : ℕ) [Fact p.Prime] (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (H : Subgroup (K ≃ₐ[E] K)) (hH : IsPGroup p ↥H) (hidx : ¬ p ∣ H.index)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k : ℕ)
    (hk : p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E K w)) :
    ∃ g : K ≃ₐ[E] K, p ^ k ∣ Nat.card ↥(H ⊓ NumberField.PlaceDecomp.decomp E K (g • w)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_exists_pow_dvd_natCard_inf_decomp_smul_of_isPGroup_of_not_dvd_index.solution
