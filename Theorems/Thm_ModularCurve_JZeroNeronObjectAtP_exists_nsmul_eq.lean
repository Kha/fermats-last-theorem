import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_exists_nsmul_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_nsmul_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (m : ℕ) (hm : 0 < m) (s : SchemeHomOver Λ.σA O.g) :
    ∃ z : SchemeHomOver Λ.σA O.g, O.L.nsmul Λ.σA m z = s := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_nsmul_eq.solution
