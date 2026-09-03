import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField
attribute [-instance] ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField
    {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (Kw : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K Kw] [IsGalois K Kw]
    (htame : ¬ p ∣ Module.finrank K Kw)
    (M : Rep.{0} (ZMod p) (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) [FiniteDimensional (ZMod p) M]
    (htriv : ∀ s ∈ Kw.fixingSubgroup, M.ρ s = 1)
    (hχ : ∀ s ∈ Kw.fixingSubgroup,
      cycloChar p (localGaloisToGlobal p ((IntermediateField.fixingSubgroupEquiv K).symm s)) = 1) :
    Module.finrank (ZMod p) (continuousH1 ((localGaloisToGlobal p).comp ((K.fixingSubgroup.subtype).comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)) M)
      = Module.finrank (ZMod p) M.ρ.invariants
        + Module.finrank (ZMod p) (M.dualTwist ((cycloChar p).comp ((localGaloisToGlobal p).comp ((K.fixingSubgroup.subtype).comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)))).ρ.invariants
        + Module.finrank ℚ_[p] K * Module.finrank (ZMod p) M := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.solution
