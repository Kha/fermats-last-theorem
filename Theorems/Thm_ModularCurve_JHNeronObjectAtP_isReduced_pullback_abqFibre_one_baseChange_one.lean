import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_isReduced_pullback_abqFibre_one_baseChange_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.isReduced_pullback_abqFibre_one_baseChange_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM A) (O : ModularCurve.JHNeronObjectAtP p M H hpM A hA Λ) :
    IsReduced (Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_isReduced_pullback_abqFibre_one_baseChange_one.solution
