import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.muBaseChange_toricLift_degeneracyHom_eq_one
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) (i : Fin 2) :
    muBaseChange (residue ↥A) O.toricRank m ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫ (O.degeneracyHom i).1 =
      (Λ.L.one (muStr (ResidueField ↥A) O.toricRank m ≫ resPt A ≫ Λ.σA)).1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one.solution
