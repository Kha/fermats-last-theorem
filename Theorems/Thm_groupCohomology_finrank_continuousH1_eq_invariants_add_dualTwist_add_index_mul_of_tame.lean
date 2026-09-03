import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame
attribute [-instance] ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p)
    (S : Subgroup (primeLocalGaloisGroup q)) (N : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) N]
    (htame : ∃ S₀ : Subgroup (primeLocalGaloisGroup q), S₀ ≤ S ∧
      (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
        F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S₀) ∧
      (S₀.subgroupOf S).Normal ∧
      (∀ s : S, (s : primeLocalGaloisGroup q) ∈ S₀ → N.ρ s = 1 ∧ cycloChar p (primeLocalToGlobal q s) = 1) ∧
      ¬ p ∣ (S₀.subgroupOf S).index) :
    Module.finrank (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) N)
      = Module.finrank (ZMod p) N.ρ.invariants
        + Module.finrank (ZMod p)
            (N.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants
        + S.index * Module.finrank (ZMod p) N := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame.solution
