import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_primeLocalPlace_isPrimitiveRoot_apply_div
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ExtCitation.LocalLevel.coe_smul_OO

open ExtCitation

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_primeLocalPlace_isPrimitiveRoot_apply_div
    (q : Nat.Primes) {m : ℕ}
    (hqm : ¬ (q : ℕ) ∣ m) {α : AlgebraicClosure ℚ} (hα : α ^ m = ((q : ℕ) : AlgebraicClosure ℚ)) :
    ∃ σ ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ, IsPrimitiveRoot (σ α / α) m := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_primeLocalPlace_isPrimitiveRoot_apply_div.solution
