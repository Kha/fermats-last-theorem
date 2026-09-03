import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_toricPts_mul_le_sup_of_coprime

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.toricPts_mul_le_sup_of_coprime
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    O.toricPts (a * b) ≤ O.toricPts a ⊔ O.toricPts b := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_mul_le_sup_of_coprime.solution
