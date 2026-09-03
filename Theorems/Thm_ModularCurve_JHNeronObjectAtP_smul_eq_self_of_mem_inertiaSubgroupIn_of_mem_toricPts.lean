import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hmp : m.Coprime p) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ y ∈ O.toricPts m, σ • y = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_toricPts.solution
