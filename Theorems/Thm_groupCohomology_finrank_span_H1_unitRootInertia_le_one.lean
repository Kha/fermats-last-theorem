import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_span_H1_unitRootInertia_le_one
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.continuousH2ToH2_mk ExtCitation.LocalLevel.coe_smul_OO groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π groupCohomology.cup_apply groupCohomology.cupCochain_apply groupCohomology.H1desc_H1π IsLocalRing.principalUnits_zero groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem groupCohomology.finrank_span_H1_unitRootInertia_le_one
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (N : Rep k (primeLocalGaloisGroup (pPrime p))) (hN : Module.finrank k N = 1)
    (hcyc : ∀ (σ : primeLocalGaloisGroup (pPrime p)),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ∀ c : ℕ,
        (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ c) →
          ∀ m : N, N.ρ σ m = (c : k) • m)
    (hsm : ∀ m : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : primeLocalGaloisGroup (pPrime p), primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup →
        N.ρ s m = m) :
    FiniteDimensional k (Submodule.span k
        {x : H1 N | ∃ y : cocycles₁ N,
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
            ∀ (g s : primeLocalGaloisGroup (pPrime p)),
              primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → y.val (g * s) = y.val g) ∧
          (∀ σ ∈ ResidualGaloisRep.unitRootInertia p, y.val σ = 0) ∧
          x = (H1π N).hom y}) ∧
      Module.finrank k (Submodule.span k
        {x : H1 N | ∃ y : cocycles₁ N,
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
            ∀ (g s : primeLocalGaloisGroup (pPrime p)),
              primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → y.val (g * s) = y.val g) ∧
          (∀ σ ∈ ResidualGaloisRep.unitRootInertia p, y.val σ = 0) ∧
          x = (H1π N).hom y}) ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_span_H1_unitRootInertia_le_one.solution
