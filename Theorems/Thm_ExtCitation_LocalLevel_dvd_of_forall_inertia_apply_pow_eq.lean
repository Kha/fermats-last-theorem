import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_dvd_of_forall_inertia_apply_pow_eq
attribute [-instance] ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO

open ExtCitation
theorem ExtCitation.LocalLevel.dvd_of_forall_inertia_apply_pow_eq (q : Nat.Primes) {n : ℕ} (hn : 0 < n) (hqn : ¬ (q : ℕ) ∣ n)
    {α : AlgebraicClosure ℚ} (hα : α ^ n = ((q : ℕ) : AlgebraicClosure ℚ)) (N : ℕ)
    (h : ∀ i ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q),
      primeLocalToGlobal q i (α ^ N) = α ^ N) :
    n ∣ N := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_dvd_of_forall_inertia_apply_pow_eq.solution
