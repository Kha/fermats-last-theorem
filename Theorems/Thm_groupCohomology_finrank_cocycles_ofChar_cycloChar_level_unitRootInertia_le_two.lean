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
import P2M.Sol.S_groupCohomology_finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.continuousH2ToH2_mk ExtCitation.LocalLevel.coe_smul_OO

set_option autoImplicit false

open CategoryTheory TrivSqZeroExt ExtCitation open groupCohomology hiding isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar

theorem groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Z : Submodule (ZMod p)
      (cocycles₁ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal (pPrime p))))))
    (hZ : ∀ c, c ∈ Z ↔
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup (pPrime p)),
          primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
      ∀ σ ∈ ResidualGaloisRep.unitRootInertia p, c.val σ = 0) :
    FiniteDimensional (ZMod p) Z ∧ Module.finrank (ZMod p) Z ≤ 2 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two.solution
