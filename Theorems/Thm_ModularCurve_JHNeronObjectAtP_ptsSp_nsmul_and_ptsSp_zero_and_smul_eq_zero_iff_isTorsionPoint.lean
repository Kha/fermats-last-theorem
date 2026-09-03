import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing
open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    (∀ (k : ℕ) (z : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),
      O.ptsSp (k • z) = O.L.nsmul (resPt A ≫ Λ.σA) k (O.ptsSp z)) ∧
    O.ptsSp 0 = O.L.one (resPt A ≫ Λ.σA) ∧
    (∀ (k : ℕ) (z : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),
      k • z = 0 ↔ O.L.IsTorsionPoint (resPt A ≫ Λ.σA) k (O.ptsSp z)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint.solution
