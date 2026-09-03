import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import P2M.Util
namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPts_of_pos

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (hm : 0 < m) :
    O.toricPts m = AddSubgroup.closure (Set.range (O.toricPoint m hm)) := by
  rw [toricPts, dif_pos hm]
