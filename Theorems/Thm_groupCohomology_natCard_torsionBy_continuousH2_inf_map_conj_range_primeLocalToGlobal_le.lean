import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal
attribute [-simp] groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero

set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation

theorem groupCohomology.natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Finite ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ∧
    Nat.card ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ≤ p := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le.solution
